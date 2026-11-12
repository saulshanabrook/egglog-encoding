//! Prove that redundant names may be permuted.

use super::*;

impl SlotLifter<'_, NativeProofs<'_>> {
    /// Prove a permutation fixing the support names free in the current term.
    pub(super) fn support_permutation(
        &mut self,
        support: Support,
        class: TermId,
        permutation: &Renaming,
    ) -> LiftResult<ViewId> {
        let support = self.resolve_support(support)?;
        let (base, _) = self.support_basis(support.origin)?;
        let term = self.dec(class)?;
        let free = self.program.free_slots(&self.out.term_dag, term);
        let slots = self.support_slots(support)?;
        if (support.transport.is_none() && base != class)
            || slots
                .intersection(&free)
                .any(|&slot| permutation.apply(slot) != slot)
        {
            return Err("the requested permutation moves a recorded support slot".into());
        }
        let existence = if let Some(transport) = support.transport {
            let reverse = self.out.sym(transport);
            let proof = self.trans(transport, reverse)?;
            self.existence_from(proof, term)?
        } else {
            match support.origin {
                SupportOrigin::Row {
                    proof,
                    column: Some(_),
                } => {
                    let edge = self.eq(proof)?;
                    self.orient(edge, class, class)?
                }
                SupportOrigin::Row {
                    proof,
                    column: None,
                } => self.support_class(proof, true)?,
                SupportOrigin::Equality { proof, .. } => {
                    let reverse = self.out.sym(proof);
                    self.trans(proof, reverse)?
                }
                SupportOrigin::Constructor { .. } => unreachable!("support was resolved"),
            }
        };
        let mut proof = existence;
        let mut visited = BTreeSet::new();
        for (start, _) in permutation.entries() {
            if !visited.insert(start) {
                continue;
            }
            let mut a = start;
            let mut b = permutation.apply(a);
            while b != start {
                visited.insert(b);
                let fresh = self.fresh();
                let swap = |this: &mut Self, slot| {
                    if free.contains(&slot) {
                        // An older support may contain names absent from this
                        // term. Transport swaps only for its current free names.
                        if let Some(transport) = support.transport {
                            let coordinates = this.out.edge(transport).renaming.inverse();
                            let (slot, fresh) = (coordinates.apply(slot), coordinates.apply(fresh));
                            let swap = Renaming::new([(slot, fresh), (fresh, slot)]).unwrap();
                            let certificate = this.support_permutation(
                                Support {
                                    transport: None,
                                    ..support
                                },
                                base,
                                &swap,
                            )?;
                            return this.transport(certificate, transport);
                        }
                        match support.origin {
                            SupportOrigin::Row {
                                proof,
                                column: Some(column),
                            } => this.edge_certificate(proof, column, true, slot, fresh),
                            SupportOrigin::Row {
                                proof,
                                column: None,
                            } => this.cert_from(proof, class, slot, fresh),
                            SupportOrigin::Equality { proof, .. } => this.lemma(proof, slot, fresh),
                            SupportOrigin::Constructor { .. } => {
                                unreachable!("support was resolved")
                            }
                        }
                    } else {
                        let renaming = Renaming::new([(slot, fresh), (fresh, slot)]).unwrap();
                        let target = rename(&mut this.out.term_dag, &renaming, term);
                        let ordinary = this.out.proof(existence);
                        let ordinary = this.out.alpha(ordinary, target);
                        Ok(this.out.view(ordinary, term, renaming))
                    }
                };
                let left = swap(self, a)?;
                let right = swap(self, b)?;
                let exchange = self.trans(left, right)?;
                let exchange = self.trans(exchange, left)?;
                proof = self.trans(proof, exchange)?;
                a = b;
                b = permutation.apply(b);
            }
        }
        Ok(proof)
    }

    pub(super) fn transport_support(
        &mut self,
        mut support: Support,
        transport: ViewId,
    ) -> LiftResult<Support> {
        support.transport = Some(match support.transport {
            Some(previous) => self.trans(transport, previous)?,
            None => transport,
        });
        Ok(support)
    }

    pub(super) fn support_slots(&mut self, support: Support) -> LiftResult<BTreeSet<i64>> {
        let support = self.resolve_support(support)?;
        let (_, slots) = self.support_basis(support.origin)?;
        Ok(slots
            .into_iter()
            .map(|slot| {
                support
                    .transport
                    .map_or(slot, |proof| self.out.edge(proof).renaming.apply(slot))
            })
            .collect())
    }

    /// Constructor support is needed only when an alignment transports names.
    /// Follow its recorded derivation after the ordinary term alignment path.
    fn resolve_support(&mut self, support: Support) -> LiftResult<Support> {
        let SupportOrigin::Constructor { proof, column, rhs } = support.origin else {
            return Ok(support);
        };
        let resolved = self.row_child_support(proof, column, rhs)?;
        if let Some(transport) = support.transport {
            return self.transport_support(resolved, transport);
        }
        Ok(resolved)
    }

    fn support_basis(&self, origin: SupportOrigin) -> LiftResult<(TermId, BTreeSet<i64>)> {
        match origin {
            SupportOrigin::Row { proof, column } => {
                let (head, args) = self
                    .app(self.egg.get(proof).rhs())
                    .ok_or("support is not a row")?;
                let slots = self.slot_map(args[1])?;
                let range_column = if matches!(row_kind(head), RowKind::Invocation) {
                    Some(2)
                } else {
                    Some(0)
                };
                let slots = if column == range_column {
                    slots.values().copied().collect()
                } else {
                    slots.keys().copied().collect()
                };
                Ok((args[column.unwrap_or(0)], slots))
            }
            SupportOrigin::Equality { class, proof } => {
                let edge = self.out.edge(proof);
                let lhs = self.program.free_slots(&self.out.term_dag, edge.lhs);
                let rhs = self.program.free_slots(&self.out.term_dag, edge.rhs);
                Ok((class, lhs.intersection(&rhs).copied().collect()))
            }
            SupportOrigin::Constructor { .. } => unreachable!("support was resolved"),
        }
    }

    /// A redundant-slot certificate for the selected endpoint of an equality row.
    pub(super) fn edge_certificate(
        &mut self,
        proof: ProofId,
        column: usize,
        rhs: bool,
        slot: i64,
        fresh: i64,
    ) -> LiftResult<ViewId> {
        let p = self.egg.get(proof).clone();
        match p.justification() {
            Justification::Sym(inner) => {
                return self.edge_certificate(*inner, column, !rhs, slot, fresh);
            }
            Justification::Trans(a, b) => {
                return self.edge_certificate(if rhs { *b } else { *a }, column, rhs, slot, fresh);
            }
            Justification::Congr { proof: base, .. } if !rhs => {
                return self.edge_certificate(*base, column, false, slot, fresh);
            }
            _ => {}
        }
        let row = if rhs { p.rhs() } else { p.lhs() };
        let (head, args) = self.app(row).ok_or("leader edge is not a row")?;
        let class = args[column];
        if let Justification::Rule { premise_proofs, .. } = p.justification()
            && let Some(support) = self.function_premise(premise_proofs, "FreeVars_", class)?
            && !self.support_slots(Support::new(support))?.contains(&slot)
        {
            return self.cert_from(support, class, slot, fresh);
        }
        let lhs_column = if matches!(row_kind(head), RowKind::Invocation) {
            2
        } else {
            0
        };
        let mut bridge = if rhs {
            self.eq(proof)?
        } else {
            self.row_eq(proof, false)?
        };
        if column != lhs_column {
            bridge = self.out.sym(bridge);
        }
        let prop = self.out.edge(bridge).clone();
        let content = rename(&mut self.out.term_dag, &prop.renaming, prop.rhs);
        if !self
            .program
            .free_slots(&self.out.term_dag, content)
            .contains(&slot)
        {
            return self.lemma(bridge, slot, fresh);
        }
        match p.justification() {
            Justification::Rule {
                name,
                premise_proofs,
                substitution,
            } => {
                if matches!(rule_kind(self.program, name), RuleKind::Invocation) {
                    let edge = premise_proofs[0];
                    if column == 2 {
                        let invocation = self.row_eq(proof, rhs)?;
                        let renaming = self.out.edge(invocation).renaming.inverse();
                        let certificate = self.edge_certificate(
                            proof,
                            0,
                            rhs,
                            renaming.apply(slot),
                            renaming.apply(fresh),
                        )?;
                        return self.transport(certificate, invocation);
                    }
                    let m = self.slot_map(self.sub(substitution, "_m")?)?;
                    let group = self.group(self.sub(substitution, "_grp")?)?;
                    let (index, _) =
                        crate::slotted::runtime::group::coset_min_with_index(&m, &group)
                            .ok_or("coset-min has an empty group")?;
                    if !group[index].contains_key(&slot) {
                        return self.group_certificate(
                            class,
                            &group[index],
                            premise_proofs[1],
                            slot,
                            fresh,
                        );
                    }
                    let symmetry = self.symmetry(class, &group[index], premise_proofs[1])?;
                    let renaming = self.out.edge(symmetry).renaming.clone();
                    let certificate = self.edge_certificate(
                        edge,
                        2,
                        true,
                        renaming.apply(slot),
                        renaming.apply(fresh),
                    )?;
                    let reverse = self.out.sym(symmetry);
                    return self.transport(certificate, reverse);
                }
                if matches!(rule_kind(self.program, name), RuleKind::BinderStrip) {
                    let prior = premise_proofs[0];
                    let (_, mapping, _) = self.row_sides(self.egg.get(prior).rhs())?;
                    let retained = if column == 0 {
                        mapping.values().any(|&value| value == slot)
                    } else {
                        mapping.contains_key(&slot)
                    };
                    if !retained {
                        return self.edge_certificate(prior, column, true, slot, fresh);
                    }
                    let mut bridge = self.row_eq(prior, true)?;
                    if column == 2 {
                        bridge = self.out.sym(bridge);
                    } else {
                        bridge = self.orient(bridge, class, class)?;
                    }
                    return self.lemma(bridge, slot, fresh);
                }
                if matches!(rule_kind(self.program, name), RuleKind::SeedIdentity) {
                    return Err("identity support includes the requested redundant slot".into());
                }
                let other = args[2 - column];
                let other = self.support_premise(premise_proofs, other)?;
                let inverse = prop.renaming.inverse();
                let prior_slot = inverse.apply(slot);
                if !self
                    .support_slots(Support::new(other))?
                    .contains(&prior_slot)
                {
                    let (_, args) = self
                        .app(self.egg.get(other).rhs())
                        .ok_or("support is not a row")?;
                    let certificate =
                        self.cert_from(other, args[0], prior_slot, inverse.apply(fresh))?;
                    return self.transport(certificate, bridge);
                }
                if matches!(rule_kind(self.program, name), RuleKind::RestateEdge) {
                    return self.edge_certificate(premise_proofs[0], column, true, slot, fresh);
                }
                Err("leader edge omits a slot retained by both recorded endpoint supports".into())
            }
            Justification::Congr {
                proof: base,
                child_index,
                child_proof,
            } => {
                if *child_index != column {
                    return self.edge_certificate(*base, column, true, slot, fresh);
                }
                let bridge = self.eq(*child_proof)?;
                let renaming = self.out.edge(bridge).renaming.clone();
                let certificate = self.edge_certificate(
                    *base,
                    column,
                    true,
                    renaming.apply(slot),
                    renaming.apply(fresh),
                )?;
                let bridge = self.out.sym(bridge);
                self.transport(certificate, bridge)
            }
            other => Err(format!(
                "leader edge support has no recorded premise through {other:?}"
            )),
        }
    }

    pub(super) fn support_premise(
        &self,
        premises: &[ProofId],
        class: TermId,
    ) -> LiftResult<ProofId> {
        self.function_premise(premises, "FreeVars_", class)?
            .ok_or_else(|| format!("no support premise for class {class}"))
    }

    pub(super) fn optional_support(
        &self,
        premises: &[ProofId],
        class: TermId,
    ) -> LiftResult<Option<Support>> {
        Ok(self
            .function_premise(premises, "FreeVars_", class)?
            .map(Support::new))
    }

    fn row_child_support(
        &mut self,
        proof: ProofId,
        column: usize,
        rhs: bool,
    ) -> LiftResult<Support> {
        let p = self.egg.get(proof).clone();
        match p.justification() {
            Justification::Sym(inner) => self.row_child_support(*inner, column, !rhs),
            Justification::Trans(a, b) => {
                self.row_child_support(if rhs { *b } else { *a }, column, rhs)
            }
            Justification::Congr {
                proof: base,
                child_index,
                child_proof,
            } => {
                let mut support = self.row_child_support(*base, column, rhs)?;
                if rhs {
                    let (head, _) = self
                        .app(self.egg.get(*base).rhs())
                        .ok_or("constructor support is not a row")?;
                    if self.surface_column(head, *child_index).ok() == Some(column) {
                        let bridge = self.eq(*child_proof)?;
                        let bridge = self.out.sym(bridge);
                        support = self.transport_support(support, bridge)?;
                    }
                }
                Ok(support)
            }
            Justification::Rule {
                name,
                premise_proofs,
                ..
            } => match rule_kind(self.program, name) {
                RuleKind::ChildUpdate => {
                    let row = self.egg.get(premise_proofs[1]).rhs();
                    let updated = self.updated_column(name, row)?;
                    if column == updated {
                        Ok(Support {
                            origin: SupportOrigin::Row {
                                proof: premise_proofs[0],
                                column: Some(2),
                            },
                            transport: None,
                        })
                    } else {
                        self.row_child_support(premise_proofs[1], column, true)
                    }
                }
                RuleKind::Migration => self.row_child_support(premise_proofs[1], column, true),
                RuleKind::BinderRefresh => self.row_child_support(premise_proofs[0], column, true),
                RuleKind::Apply(_) => {
                    let row = if rhs { p.rhs() } else { p.lhs() };
                    let (head, args) = self.app(row).ok_or("constructor support is not a row")?;
                    let (_, _, physical) = self.program.constructors[head]
                        .encoded_columns()
                        .nth(column)
                        .ok_or("constructor column is missing")?;
                    let class = args[physical.end - 1];
                    if let Some(&certificate) = self.head_supports.get(&(proof, column)) {
                        let certificate = self.out.plain(certificate);
                        return self.equality_support(class, certificate);
                    }
                    let edge = self.slot_map(args[physical.start])?;
                    let term = self.dec(class)?;
                    // An unrestricted construction proves structural support.
                    // Restricted input edges inherit the match's support evidence.
                    if self
                        .program
                        .free_slots(&self.out.term_dag, term)
                        .iter()
                        .all(|slot| edge.contains_key(slot))
                    {
                        return self.structural_child_support(proof, physical.end - 1, rhs);
                    }
                    Err(format!(
                        "restricted constructed child {class} at proof {proof}, column {column} lacks its source support certificate"
                    ))
                }
                other => Err(format!(
                    "constructor child support through {other:?} at {proof}, column {column}"
                )),
            },
            Justification::Fiat => {
                let row = if rhs { p.rhs() } else { p.lhs() };
                let (head, _) = self.app(row).ok_or("constructor support is not a row")?;
                let (_, _, physical) = self.program.constructors[head]
                    .encoded_columns()
                    .nth(column)
                    .ok_or("constructor column is missing")?;
                let physical = physical.end - 1;
                self.structural_child_support(proof, physical, rhs)
            }
            other => Err(format!(
                "constructor child support through {other:?} at {proof}, column {column}"
            )),
        }
    }

    fn structural_child_support(
        &mut self,
        proof: ProofId,
        physical: usize,
        rhs: bool,
    ) -> LiftResult<Support> {
        let statement = self.egg.get(proof);
        let row = if rhs {
            statement.rhs()
        } else {
            statement.lhs()
        };
        let (_, args) = self.app(row).ok_or("constructor support is not a row")?;
        let class = args[physical];
        let term = self.dec(class)?;
        let child = self.project_side(proof, physical, rhs)?;
        let proof = self.existence_from(child, term)?;
        self.equality_support(class, proof)
    }

    fn equality_support(&mut self, class: TermId, proof: ViewId) -> LiftResult<Support> {
        let mut proof = self.content_form(proof);
        let lhs = self.out.edge(proof).lhs;
        let expected = self.dec(class)?;
        if lhs != expected {
            let coordinates = self
                .term_coordinates(lhs, expected)
                .ok_or("support equality has the wrong input class")?;
            proof = self.rename_both(proof, &coordinates);
            proof = self.content_form(proof);
            let reverse = self.out.sym(proof);
            let reverse = self.out.proof(reverse);
            let reverse = self.out.alpha(reverse, expected);
            let reverse = self.out.plain(reverse);
            proof = self.out.sym(reverse);
        }
        let proof = self.content_form(proof);
        let edge = self.out.edge(proof).clone();
        let free = self.program.free_slots(&self.out.term_dag, edge.lhs);
        let rhs = self
            .program
            .refresh_binders_avoiding(&mut self.out.term_dag, edge.rhs, &free);
        let ordinary = self.out.proof(proof);
        let ordinary = self.out.alpha(ordinary, rhs);
        let proof = self.out.plain(ordinary);
        Ok(Support {
            origin: SupportOrigin::Equality { class, proof },
            transport: None,
        })
    }

    /// Establish the class named by the selected endpoint of a support row.
    pub(super) fn support_class(&mut self, proof: ProofId, rhs: bool) -> LiftResult<ViewId> {
        let p = self.egg.get(proof);
        match p.justification() {
            Justification::Sym(inner) => return self.support_class(*inner, !rhs),
            Justification::Trans(a, b) => {
                return self.support_class(if rhs { *b } else { *a }, rhs);
            }
            Justification::Congr { proof: base, .. } if !rhs => {
                return self.support_class(*base, false);
            }
            _ => {}
        }
        let row = if rhs { p.rhs() } else { p.lhs() };
        let (head, args) = self.app(row).ok_or("support evidence is not a row")?;
        if !head.starts_with("FreeVars_") {
            return Err(format!(
                "expected support evidence, got {}",
                self.egg_string(row)
            ));
        }
        let class = args[0];
        let evidence = match p.justification().clone() {
            Justification::Rule {
                name,
                premise_proofs,
                ..
            } => match rule_kind(self.program, &name) {
                RuleKind::ClassSlots | RuleKind::TransportUp | RuleKind::TransportDown => {
                    self.eq(premise_proofs[0])?
                }
                RuleKind::SlotClosure => {
                    let prior = self.support_premise(&premise_proofs, class)?;
                    self.support_class(prior, true)?
                }
                other => return Err(format!("no class witness through support rule {other:?}")),
            },
            Justification::MergeFn { old_proof, .. } => self.support_class(old_proof, true)?,
            Justification::Congr {
                proof: base,
                child_index,
                child_proof,
            } => {
                if child_index == 0 {
                    self.eq(child_proof)?
                } else {
                    self.support_class(base, true)?
                }
            }
            other => {
                return Err(format!(
                    "no class witness through support evidence {other:?}"
                ));
            }
        };
        self.orient(evidence, class, class)
    }

    /// The certificate for `(c, s, f)` through one proof of a `FreeVars` row
    /// that excludes `s`.
    pub(super) fn cert_from(
        &mut self,
        proof: ProofId,
        c: TermId,
        s: i64,
        f: i64,
    ) -> LiftResult<ViewId> {
        self.cert_side(proof, true, c, s, f)
    }

    /// Prove a fresh swap for a class slot omitted by its recorded constructor row.
    pub(super) fn node_certificate(
        &mut self,
        proof: ProofId,
        s: i64,
        f: i64,
    ) -> LiftResult<ViewId> {
        // the class is the row, `c = M·row`: a slot the row's content does
        // not mention is redundant outright; otherwise s is not a node slot
        // of the row, so it belongs to a child's term, where the child's
        // class does not depend on it
        let row = self.egg.get(proof).rhs();
        let row_eq = self.eq(proof)?; // c = M·row
        let prop = self.out.edge(row_eq).clone();
        let content = rename(&mut self.out.term_dag, &prop.renaming, prop.rhs);
        if !all_slots(&self.out.term_dag, content).contains(&s) {
            return self.lemma(row_eq, s, f);
        }
        let m_inv = prop.renaming.inverse();
        let (s_row, f_row) = (m_inv.apply(s), m_inv.apply(f));
        let (head, args) = self.app(row).ok_or("not a row")?;
        let ctor = self
            .program
            .constructors
            .get(head)
            .ok_or("unknown constructor")?
            .clone();
        let mut i = 0;
        for (j, col) in ctor.columns.iter().enumerate() {
            match col {
                ColumnKind::Child => {
                    let child = args[i + 1];
                    i += 2;
                    let completion = self.edge_memo[&(row, j)].clone();
                    let child_term = self.dec(child)?;
                    let occ = rename(&mut self.out.term_dag, &completion, child_term);
                    if !all_slots(&self.out.term_dag, occ).contains(&s_row) {
                        continue;
                    }
                    let r = completion.inverse().apply(s_row);
                    let fi = completion.inverse().apply(f_row);
                    let swap = Renaming::new([(r, fi), (fi, r)]).unwrap();
                    let cert = if self
                        .program
                        .free_slots(&self.out.term_dag, child_term)
                        .contains(&r)
                    {
                        let support = self.row_child_support(proof, j, true)?;
                        self.support_permutation(support, child, &swap)?
                    } else {
                        let existence = self.reflexive(child_term)?;
                        let target = rename(&mut self.out.term_dag, &swap, child_term);
                        let existence = self.out.proof(existence);
                        let existence = self.out.alpha(existence, target);
                        self.out.view(existence, child_term, swap)
                    };
                    let lifted = self.rename_both(cert, &completion); // occ = ·child
                    let lifted = self.out.reframe(lifted, completion.clone()); // occ = (s f)·occ
                    let lifted = self.note(lifted);
                    let refl = self.reflexive(prop.rhs)?;
                    let r = self.out.congr(refl, j, lifted).map_err(|e| e.to_string())?; // row = ·row[s->f]
                    let r = self.note(r);
                    let r = self
                        .out
                        .reframe(r, Renaming::new([(s_row, f_row), (f_row, s_row)]).unwrap());
                    let r = self.note(r); // row = (s_row f_row)·row
                    // and the class is the row
                    return self.transport(r, row_eq);
                }
                ColumnKind::Var | ColumnKind::Binder => i += 1,
                ColumnKind::Payload(_) => i += 1,
            }
        }
        Err(format!("${s} is in no child of {}", self.egg_string(row)))
    }

    fn cert_side(
        &mut self,
        proof: ProofId,
        rhs: bool,
        c: TermId,
        s: i64,
        f: i64,
    ) -> LiftResult<ViewId> {
        let p = self.egg.get(proof).clone();
        match p.justification() {
            Justification::Sym(inner) => return self.cert_side(*inner, !rhs, c, s, f),
            Justification::Trans(left, right) => {
                return self.cert_side(if rhs { *right } else { *left }, rhs, c, s, f);
            }
            Justification::Congr { proof: base, .. } if !rhs => {
                return self.cert_side(*base, false, c, s, f);
            }
            _ => {}
        }
        let row = if rhs { p.rhs() } else { p.lhs() };
        let (head, args) = self.app(row).ok_or("support evidence is not a row")?;
        if !head.starts_with("FreeVars_") || args.first() != Some(&c) {
            return Err(format!(
                "expected support evidence for {}, got {}",
                self.egg_string(c),
                self.egg_string(row)
            ));
        }
        if self.slot_map(args[1])?.contains_key(&s) {
            return Err(format!(
                "support evidence {} still includes ${s}",
                self.egg_string(row)
            ));
        }
        let term = self.dec(c)?;
        if !self
            .program
            .free_slots(&self.out.term_dag, term)
            .contains(&s)
        {
            let existence = self.support_class(proof, rhs)?;
            return self.lemma(existence, s, f);
        }
        match p.justification().clone() {
            Justification::Rule {
                name,
                premise_proofs: prems,
                substitution: subst,
            } => match rule_kind(self.program, &name) {
                RuleKind::ClassSlots => self.node_certificate(prems[0], s, f),
                RuleKind::TransportDown => {
                    // FreeVars b ⊆ m⁻¹(FreeVars a) from a = m·b
                    let edge = self.eq(prems[0])?; // a = m·b
                    let q = self.out.sym(edge); // b = m⁻¹·a
                    let q = self.note(q);
                    let prop = self.out.edge(q).clone();
                    let a_term = prop.rhs;
                    let content = rename(&mut self.out.term_dag, &prop.renaming, a_term);
                    if !all_slots(&self.out.term_dag, content).contains(&s) {
                        return self.lemma(q, s, f);
                    }
                    // the slot of a it comes from is redundant in a
                    let x = prop.renaming.inverse().apply(s);
                    let a = self.sub(&subst, "_a")?;
                    let fa = prop.renaming.inverse().apply(f);
                    let prior = self.support_premise(&prems, a)?;
                    let cert_a = self.cert_from(prior, a, x, fa)?;
                    self.transport(cert_a, q)
                }
                RuleKind::TransportUp => {
                    // FreeVars a ⊆ m(FreeVars b) from a = m·b
                    let edge = self.eq(prems[0])?; // a = m·b
                    let prop = self.out.edge(edge).clone();
                    let content = rename(&mut self.out.term_dag, &prop.renaming, prop.rhs);
                    if !all_slots(&self.out.term_dag, content).contains(&s) {
                        return self.lemma(edge, s, f);
                    }
                    let r = prop.renaming.inverse().apply(s);
                    let b = self.sub(&subst, "_b")?;
                    let fb = prop.renaming.inverse().apply(f);
                    let prior = self.support_premise(&prems, b)?;
                    let cert_b = self.cert_from(prior, b, r, fb)?;
                    self.transport(cert_b, edge)
                }
                RuleKind::SlotClosure => {
                    let grp = self.group(self.sub(&subst, "_grp")?)?;
                    let old = self.slot_map(self.sub(&subst, "_slots")?)?;
                    if !old.contains_key(&s) {
                        // Closure also preserves names already proved absent;
                        // no symmetry needs to move such a name out of the set.
                        let prior = self.support_premise(&prems, c)?;
                        return self.cert_from(prior, c, s, f);
                    }
                    let mut removal = None;
                    crate::slotted::runtime::group::slot_closure_with(
                        &grp,
                        &old,
                        |slot, index, reverse| {
                            if slot == s {
                                removal = Some((index, reverse));
                            }
                        },
                    );
                    let (index, reverse) =
                        removal.ok_or("slot closure did not remove the requested slot")?;
                    let group = self.group_premise(&prems, c)?;
                    let mut symmetry = self.symmetry(c, &grp[index], group)?;
                    if reverse {
                        symmetry = self.out.sym(symmetry);
                    }
                    let prop = self.out.edge(symmetry).clone();
                    let t = self.dec(c)?;
                    let content = rename(&mut self.out.term_dag, &prop.renaming, t);
                    if !all_slots(&self.out.term_dag, content).contains(&s) {
                        return self.lemma(symmetry, s, f);
                    }
                    let prior_slot = prop.renaming.inverse().apply(s);
                    if old.contains_key(&prior_slot) {
                        if reverse {
                            return self.group_certificate(c, &grp[index], group, s, f);
                        }
                        let certificate = self.group_certificate(
                            c,
                            &grp[index],
                            group,
                            prior_slot,
                            prop.renaming.inverse().apply(f),
                        )?;
                        return self.transport(certificate, symmetry);
                    }
                    let fresh = self.fresh();
                    let prior = self.support_premise(&prems, c)?;
                    let certificate = self.cert_from(prior, c, prior_slot, fresh)?;
                    let back = self.out.sym(symmetry);
                    let proof = self.trans(symmetry, certificate)?;
                    let proof = self.trans(proof, back)?;
                    Ok(self.retarget(proof, fresh, f))
                }
                other => Err(format!("no certificate through rule {other:?}")),
            },
            Justification::MergeFn {
                old_proof,
                new_proof,
                ..
            } => {
                for side in [old_proof, new_proof] {
                    let t = self.egg.get(side).rhs();
                    if let Some((_, args)) = self.app(t)
                        && let Some(cs) = renaming_from_term(self.egg(), args[1])
                        && !cs.contains_key(&s)
                    {
                        return self.cert_from(side, c, s, f);
                    }
                }
                Err("neither merged slot set excludes the slot".into())
            }
            Justification::Congr {
                proof: base,
                child_proof,
                ..
            } => {
                // the row's class moved from c0 to c: certificates transport
                let c0 = self.app(self.egg.get(base).rhs()).ok_or("not a row")?.1[0];
                let e = self.eq(child_proof)?; // c0 = n·c
                let n = self.out.edge(e).renaming.clone();
                let cert0 = self.cert_from(base, c0, n.apply(s), n.apply(f))?;
                let q = self.out.sym(e); // c = n⁻¹·c0
                let q = self.note(q);
                self.transport(cert0, q)
            }
            Justification::Trans(..) | Justification::Sym(..) => unreachable!(),
            Justification::Fiat => Err("a slot set stated by fiat".into()),
            other => Err(format!("no certificate through {other:?}")),
        }
    }

    /// From `P: L = m·R` whose content (`m·R`) has no free `s`, with `s` a
    /// slot of `L` and `f` unused: `L = (s f)·L`.
    fn lemma(&mut self, p: ViewId, s: i64, f: i64) -> LiftResult<ViewId> {
        let mut pc = self.content_form(p); // L = C
        let mut content = self.out.edge(pc).rhs;
        let mut slots = all_slots(&self.out.term_dag, content);
        if slots.contains(&s)
            && !self
                .program
                .free_slots(&self.out.term_dag, content)
                .contains(&s)
        {
            content = self.program.refresh_binders_avoiding(
                &mut self.out.term_dag,
                content,
                &BTreeSet::from([s, f]),
            );
            if content != self.out.edge(pc).rhs {
                let ordinary = self.out.proof(pc);
                let ordinary = self.out.alpha(ordinary, content);
                pc = self.out.plain(ordinary);
            }
            slots = all_slots(&self.out.term_dag, content);
        }
        if !slots.contains(&s) && slots.contains(&f) {
            // `C` must be fixed by (s f): go through a name it lacks, then
            // rename that name to `f`, which `L` lacks
            let g = self.fresh();
            let r = self.lemma(p, s, g)?; // L = (s g)·L
            let r = self.rename_both(r, &Renaming::new([(g, f), (f, g)]).unwrap()); // L = (s f)·L
            return Ok(self.note(r));
        }
        if slots.contains(&s) {
            return Err(format!(
                "the content {} still mentions ${s}",
                self.out_string(content)
            ));
        }
        let tau = Renaming::new([(s, f), (f, s)]).unwrap();
        let rb = self.rename_both(pc, &tau); // τL = τ·C
        let rb = self.out.reframe(rb, tau.clone()); // τL = C, since τ·C is C
        let back = self.out.sym(rb); // C = τL
        let r = self.trans(pc, back)?; // L = τL
        let r = self.out.reframe(r, tau); // L = τ·L
        Ok(self.note(r))
    }

    /// `L = (s f)·L` from `L = (s g)·L`, for `f` and `g` both absent from `L`.
    fn retarget(&mut self, r: ViewId, g: i64, f: i64) -> ViewId {
        if g == f {
            return r;
        }
        let r = self.rename_both(r, &Renaming::new([(g, f), (f, g)]).unwrap());
        self.note(r)
    }

    /// From `cert: X = τ·X` and `q: Y = N·X`: `Y = (N∘τ∘N⁻¹)·Y`.
    pub(super) fn transport(&mut self, cert: ViewId, q: ViewId) -> LiftResult<ViewId> {
        let left = self.trans(q, cert)?; // Y = (N∘τ)·X
        let back = self.out.sym(q); // X = N⁻¹·Y
        self.trans(left, back)
    }

    /// Apply a child proof at a path below the right-hand side of `p`.
    pub(super) fn congr_at(
        &mut self,
        p: ViewId,
        path: &[usize],
        cert: ViewId,
    ) -> LiftResult<ViewId> {
        let (first, rest) = path.split_first().ok_or("empty path")?;
        let child = if rest.is_empty() {
            cert
        } else {
            let refl = self.out.project(p, *first).map_err(|e| e.to_string())?;
            self.congr_at(refl, rest, cert)?
        };
        let r = self
            .out
            .congr(p, *first, child)
            .map_err(|e| e.to_string())?;
        Ok(self.note(r))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::slotted::{Compiler, Options, ProofMode, new_egraph_with_proofs};

    #[test]
    fn absence_certificates_preserve_shared_dags() {
        for depth in [8, 64] {
            let mut program = ProofContext::default();
            program.add_constructor("V", vec![ColumnKind::Var]);
            program.add_constructor("Z", vec![]);
            program.add_constructor("Pair", vec![ColumnKind::Child; 2]);
            let mut dag = TermDag::default();
            let zero = slot_term(&mut dag, 0);
            let lhs = dag.app("V".into(), vec![zero]);
            let one = slot_term(&mut dag, 1);
            let expected = dag.app("V".into(), vec![one]);
            let mut rhs = dag.app("Z".into(), vec![]);
            for _ in 0..depth {
                rhs = dag.app("Pair".into(), vec![rhs, rhs]);
            }
            program
                .unions
                .push(super::super::super::context::Union { lhs, rhs });
            let egg = ProofStore::new(TermDag::default(), HashMap::default(), HashSet::default());
            let names = EncodingNames::default();
            let mut lifter = SlotLifter::new(
                &program,
                dag,
                &names,
                NativeProofs {
                    store: &egg,
                    program: &[],
                },
            );
            let identity = lifter.out.fiat(lhs, lhs);
            assert!(lifter.lemma(identity, 0, 1).is_err());
            let source = lifter.out.fiat(lhs, rhs);
            let certificate = lifter.lemma(source, 0, 1).unwrap();
            let (mut store, certificate) = lifter.out.finish(certificate);
            // The large case checks DAG traversal during lifting. Check the
            // derivation on the smaller instance with the unchanged source checker.
            if depth == 8 {
                super::super::super::checker::check_proof_in_program(
                    &mut store,
                    &program,
                    certificate,
                )
                .unwrap();
            }
            assert_eq!(
                store.proposition(certificate),
                &Proposition::new(lhs, expected)
            );
        }
    }

    #[test]
    fn transported_support_discards_names_absent_from_the_current_term() {
        let mut program = ProofContext::default();
        program.add_constructor("V", vec![ColumnKind::Var]);
        program.add_constructor("Pair", vec![ColumnKind::Child; 2]);
        let mut dag = TermDag::default();
        program
            .add_union(&mut dag, "(Pair (V $0) (V $2))", "(Pair (V $0) (V $1))")
            .unwrap();
        let old = program.unions[0].lhs;
        let current = program.unions[0].rhs;
        program
            .add_union(
                &mut dag,
                "(Pair (Pair (V $0) (V $1)) (V $2))",
                "(Pair (Pair (V $0) (V $1)) (V $2))",
            )
            .unwrap();
        let parent = program.unions[1].lhs;
        let slot_two = slot_term(&mut dag, 2);
        let variable_two = dag.app("V".into(), vec![slot_two]);
        let target = dag.app("Pair".into(), vec![old, variable_two]);
        let mut encoded = TermDag::default();
        let mut map = |slot| {
            let zero = encoded.lit(Literal::Int(0));
            let slot = encoded.lit(Literal::Int(slot));
            encoded.app("map-of".into(), vec![zero, slot])
        };
        let zero = map(0);
        let one = map(1);
        let two = map(2);
        let variable = encoded.app("V".into(), vec![zero]);
        let old_class = encoded.app("Pair".into(), vec![zero, variable, two, variable]);
        let current_class = encoded.app("Pair".into(), vec![zero, variable, one, variable]);
        let egg = ProofStore::new(encoded, HashMap::default(), HashSet::default());
        let names = EncodingNames::default();
        let mut lifter = SlotLifter::new(
            &program,
            dag,
            &names,
            NativeProofs {
                store: &egg,
                program: &[],
            },
        );
        assert_eq!(lifter.dec(old_class).unwrap(), old);
        assert_eq!(lifter.dec(current_class).unwrap(), current);
        let base = lifter.out.fiat(old, old);
        let bridge = lifter.out.fiat(current, old);
        let support = Support {
            origin: SupportOrigin::Equality {
                class: old_class,
                proof: base,
            },
            transport: Some(bridge),
        };
        let occurrences = HashMap::from_iter([
            (
                vec![0],
                Occurrence {
                    cls: current_class,
                    row: None,
                    support: Some(support),
                },
            ),
            (
                vec![1],
                Occurrence {
                    cls: variable,
                    row: None,
                    support: None,
                },
            ),
        ]);
        let proof = lifter.out.fiat(parent, parent);
        let proof = lifter.fit(proof, target, &occurrences).unwrap();
        let (mut store, proof) = lifter.out.finish(proof);
        crate::slotted::proofs::checker::check_proof_in_program(&mut store, &program, proof)
            .unwrap();
        assert_eq!(store.proposition(proof), &Proposition::new(parent, target));
    }

    #[test]
    fn slot_closure_preserves_an_earlier_redundancy_certificate() {
        let mut compiler = Compiler::new(Options {
            proof_mode: ProofMode::Prove,
            ..Default::default()
        });
        let encoded = compiler
            .compile_program(
                None,
                "(datatype E (V Var) (Pair E E))
                 (let input (Pair (V $0) (V $1)))
                 (rewrite (Pair a b) (Pair a a) :name duplicate)
                 (rewrite (Pair a b) (Pair b a) :name swap)
                 (run 3)
                 (check (= input (Pair (V $2) (V $3))))",
            )
            .unwrap();
        let commands = encoded.to_string().replace("(slotted-prove 0 ", "(prove ");
        let mut graph = new_egraph_with_proofs();
        let request = encoded.proofs.values().next().unwrap();
        let mut dag = TermDag::default();
        let context = request
            .flattened
            .context(&mut dag, BTreeMap::new())
            .unwrap();
        let (egg, evidence) = super::super::tests::native_query(
            &mut graph,
            &commands,
            &context,
            &request.flattened,
            &request.names,
            dag,
        );
        let make_lifter = || {
            SlotLifter::with_evidence(
                &context,
                evidence.store.term_dag.clone(),
                &request.names,
                NativeProofs {
                    store: &egg,
                    program: graph.proof_checking_program(),
                },
                &evidence,
            )
            .unwrap()
        };
        let mut lifter = make_lifter();
        let cases: Vec<_> = egg
            .proofs()
            .filter_map(|(id, proof)| {
                let Justification::Rule {
                    name, substitution, ..
                } = proof.justification()
                else {
                    return None;
                };
                if !matches!(rule_kind(&context, name), RuleKind::SlotClosure) {
                    return None;
                }
                let class = lifter.sub(substitution, "_c").unwrap();
                let old = lifter
                    .slot_map(lifter.sub(substitution, "_slots").unwrap())
                    .unwrap();
                let (head, args) = lifter.app(proof.rhs())?;
                if !head.starts_with("FreeVars_") {
                    return None;
                }
                let new = lifter.slot_map(args[1]).unwrap();
                let term = lifter.dec(class).unwrap();
                Some(
                    all_slots(&lifter.out.term_dag, term)
                        .into_iter()
                        .filter(|slot| !new.contains_key(slot))
                        .map(|slot| (id, class, slot, old.contains_key(&slot)))
                        .collect::<Vec<_>>(),
                )
            })
            .flatten()
            .collect();
        assert!(
            cases.iter().any(|(_, _, _, present)| !present),
            "closure must retain a previously absent slot"
        );
        assert!(
            cases.iter().any(|(_, _, _, present)| *present),
            "closure must also remove a slot through symmetry"
        );
        for (proof, class, slot, _) in cases {
            let mut lifter = make_lifter();
            let fresh = lifter.fresh();
            let term = lifter.dec(class).unwrap();
            let swap = Renaming::new([(slot, fresh), (fresh, slot)]).unwrap();
            let target = rename(&mut lifter.out.term_dag, &swap, term);
            let proof = lifter.cert_from(proof, class, slot, fresh).unwrap();
            let (mut store, proof) = lifter.out.finish(proof);
            crate::slotted::proofs::check_proof(&mut store, &request.flattened, proof).unwrap();
            assert_eq!(store.proposition(proof), &Proposition::new(term, target));
        }
    }
}
