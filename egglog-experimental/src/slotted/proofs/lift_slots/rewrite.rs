//! Instantiate source rewrites from encoded matches.

use super::*;

struct ConditionProof {
    variable: String,
    pattern: TermId,
    proof: ViewId,
    occurrences: HashMap<Vec<usize>, Occurrence>,
}

#[derive(Clone)]
pub(super) struct RuleInstance {
    proof: ViewId,
    head: ViewId,
    origin: TermId,
    occurrences: HashMap<Vec<usize>, Occurrence>,
}

pub(super) type FiringKey = (String, Vec<ProofId>, Vec<(TermId, ProofId)>);

impl SlotLifter<'_, NativeProofs<'_>> {
    fn pattern_labels(
        &self,
        names: &ProofNames,
        patterns: &[Option<TermId>],
    ) -> LiftResult<Vec<BTreeMap<String, Option<String>>>> {
        let mut atoms = Vec::new();
        for (index, positions) in names.patterns.iter().enumerate() {
            let Some(pattern) = patterns[index] else {
                continue;
            };
            for (path, root) in positions {
                let term = self.subterm_at(pattern, path)?;
                let Term::App(head, arguments) = self.out.term_dag.get(term) else {
                    return Err("source atom position is not a constructor".into());
                };
                let mut children = BTreeSet::new();
                for (column, kind) in self.program.constructors[head].columns.iter().enumerate() {
                    if *kind != ColumnKind::Child {
                        continue;
                    }
                    match self.out.term_dag.get(arguments[column]) {
                        Term::Var(variable) => {
                            children.insert(variable.clone());
                        }
                        Term::App(..) => {
                            let mut child_path = path.clone();
                            child_path.push(column);
                            if let Some((_, name)) =
                                positions.iter().find(|(path, _)| path == &child_path)
                            {
                                children.insert(name.clone());
                            }
                        }
                        Term::Lit(_) => {}
                    }
                }
                atoms.push((index, root.clone(), children));
            }
        }
        let mut labels = vec![BTreeMap::new(); patterns.len()];
        if !atoms.is_empty() {
            for (label, (pattern, root, _)) in crate::slotted::query::connected_by(
                atoms,
                |atom| atom.1.as_str(),
                |atom| atom.2.clone(),
            )
            .into_iter()
            .enumerate()
            {
                labels[pattern].insert(root, Some(format!("@atom:{label}")));
            }
        }
        Ok(labels)
    }

    pub(super) fn apply_rule(
        &mut self,
        id: ProofId,
        name: &str,
        prems: &[ProofId],
        subst: &IndexMap<String, TermId>,
        lhs: TermId,
        rhs: TermId,
    ) -> LiftResult<ViewId> {
        self.derive_rule(
            name,
            prems,
            subst,
            &HashMap::default(),
            Some((lhs, rhs)),
            Some((id, &[])),
        )
    }

    pub(super) fn derive_rule(
        &mut self,
        name: &str,
        prems: &[ProofId],
        subst: &IndexMap<String, TermId>,
        selected: &HashMap<TermId, ProofId>,
        result: Option<(TermId, TermId)>,
        head: Option<(ProofId, &[usize])>,
    ) -> LiftResult<ViewId> {
        let mut rekeys: Vec<_> = selected
            .iter()
            .map(|(&term, &proof)| (term, proof))
            .collect();
        rekeys.sort();
        let key = (name.to_owned(), prems.to_vec(), rekeys);
        let instance = if let Some(instance) = self.rule_instances.get(&key) {
            instance.clone()
        } else {
            let instance = self.instantiate_rule(name, prems, subst, selected)?;
            self.rule_instances.insert(key, instance.clone());
            instance
        };
        let p = instance.proof;
        let Some((lhs, rhs)) = result else {
            return Ok(p);
        };
        if lhs == rhs && self.is_carrier_term(lhs) {
            let built = self.dec(lhs)?;
            let (id, path) = head.ok_or("constructed rule term lacks its head position")?;
            let mut proof = instance.head;
            for &index in path {
                proof = self.out.project(proof, index).map_err(|e| e.to_string())?;
            }
            let occurrences = instance
                .occurrences
                .iter()
                .filter_map(|(at, occurrence)| {
                    at.strip_prefix(path).map(|at| (at.to_vec(), *occurrence))
                })
                .collect();
            proof = self.align_occurrences(proof, built, &occurrences, true)?;
            let proof = self.note(proof);
            let proof = self.existence_from(proof, built)?;
            self.record_head_supports(id, lhs, proof, path, &instance.occurrences)?;
            return Ok(proof);
        }
        if !self.is_carrier_term(lhs) {
            let (_, _, cls_x) = self.row_sides(lhs)?;
            let target = self.dec(cls_x)?;
            return self.align(p, target);
        }
        let built = if lhs == instance.origin {
            rhs
        } else if rhs == instance.origin {
            lhs
        } else {
            return Err("the step relates neither side with the matched class".into());
        };
        let target = self.dec(built)?;
        let p = self
            .fit(p, target, &instance.occurrences)
            .map_err(|e| format!("result of {name}: {e}"))?;
        if let Some((id, path)) = head {
            self.record_head_supports(id, built, p, path, &instance.occurrences)?;
        }
        self.orient(p, lhs, rhs)
    }

    /// Retain ordinary equality proofs for restricted children at this
    /// exact head position. Freshening every unsupported free name makes the
    /// endpoints' free-slot intersection a support certificate; later swaps use
    /// that equality and the existing absence lemma.
    fn record_head_supports(
        &mut self,
        proof: ProofId,
        row: TermId,
        parent: ViewId,
        path: &[usize],
        occurrences: &HashMap<Vec<usize>, Occurrence>,
    ) -> LiftResult<()> {
        let (head, args) = self.app(row).ok_or("constructed head is not a row")?;
        let columns = self.program.constructors[head].clone();
        for (column, kind, physical) in columns.encoded_columns() {
            if *kind != ColumnKind::Child || self.head_supports.contains_key(&(proof, column)) {
                continue;
            }
            let mut at = path.to_vec();
            at.push(column);
            let class = args[physical.end - 1];
            let edge = self.slot_map(args[physical.start])?;
            let term = self.dec(class)?;
            let free = self.program.free_slots(&self.out.term_dag, term);
            if free.iter().all(|slot| edge.contains_key(slot)) {
                continue;
            }
            let fresh = free
                .into_iter()
                .filter(|slot| !edge.contains_key(slot))
                .map(|slot| (slot, self.fresh()))
                .collect::<Vec<_>>();
            let fresh = Renaming::completing(fresh).ok_or("support freshening is not injective")?;
            let target = rename(&mut self.out.term_dag, &fresh, term);
            let child = self
                .out
                .project(parent, column)
                .map_err(|error| error.to_string())?;
            let coordinates = self.edge_memo[&(row, column)].inverse();
            let child = self.rename_both(child, &coordinates);
            let inputs = occurrences
                .iter()
                .filter_map(|(path, occurrence)| {
                    path.strip_prefix(at.as_slice())
                        .map(|path| (path.to_vec(), *occurrence))
                })
                .collect();
            let certificate = self.fit_content(child, target, &inputs)?;
            let certificate = self.out.proof(certificate);
            self.head_supports.insert((proof, column), certificate);
        }
        Ok(())
    }

    fn instantiate_rule(
        &mut self,
        name: &str,
        prems: &[ProofId],
        subst: &IndexMap<String, TermId>,
        selected: &HashMap<TermId, ProofId>,
    ) -> LiftResult<RuleInstance> {
        let rewrite = self
            .program
            .rewrites
            .get(name)
            .cloned()
            .ok_or_else(|| format!("no source for rule {name}"))?;
        let (lhs_expr, rhs_expr) = rewrite.endpoints();
        let lhs_pattern = pattern_term(&mut self.out.term_dag, lhs_expr);
        let rhs_pattern = pattern_term(&mut self.out.term_dag, rhs_expr);
        let names = self
            .names
            .get(name)
            .ok_or_else(|| format!("no generated names for rule {name}"))?;
        let root_name = match self.out.term_dag.get(lhs_pattern) {
            Term::Var(v) => v.clone(),
            _ => names.patterns[0][0].1.clone(),
        };
        let root_class = &names.classes[&root_name];
        // the stored match and its firing
        let (firing, rekeys) = self.unwrap_match(prems[0])?;
        let matched = self.egg.get(firing).clone();
        let Justification::Rule {
            premise_proofs: match_prems,
            substitution: match_subst,
            ..
        } = matched.justification().clone()
        else {
            return Err(format!("the match of {name} is not a rule firing"));
        };
        let mut bridges: HashMap<TermId, ProofId> = rekeys.into_iter().collect();
        bridges.extend(selected.iter().map(|(term, proof)| (*term, *proof)));
        let frame = {
            let m = self.sub(subst, &names.frame)?;
            frame_from_term(self.egg(), m).ok_or("the apply rule's frame is not a frame")?
        };
        // Expand the matched atoms along the patterns, recording each variable's
        // class as the rows show it; the substitution is then read off the
        // expansions' contents, lifted into the frame's slot names.
        let cls_p = self.sub(&match_subst, root_class)?;
        let selected_readings =
            self.selected_readings(firing, Some(&format!("{name}/apply")), subst)?;
        let patterns = std::iter::once(Some(lhs_pattern))
            .chain(rewrite.conditions().iter().map(|condition| {
                condition
                    .binding()
                    .map(|(_, expression)| pattern_term(&mut self.out.term_dag, expression))
            }))
            .collect::<Vec<_>>();
        let labels = self.pattern_labels(names, &patterns)?;
        let ctx = ExpandCtx {
            firing,
            root_binding: Some(root_class.clone()),
            prems: &match_prems,
            subst: &match_subst,
            names: names.patterns[0].iter().cloned().collect(),
            readings: names.readings.clone(),
            labels: &labels[0],
            selected: &selected_readings,
            bridges: &bridges,
        };
        let Expansion {
            proof: root,
            mut variables,
            occurrences: root_occ,
            slots: root_slots,
        } = self.expand(cls_p, lhs_pattern, &[], &ctx, HashMap::default())?;
        let root = if self.atom_label(ctx.labels, &root_name).is_some() {
            self.lift(root, &frame, &root_slots)?
        } else {
            let root = self.content_form(root);
            let coordinates = frame
                .ren(&root_name)
                .ok_or("matched root lacks its frame coordinates")?;
            let coordinates = self.complete(&coordinates, self.out.edge(root).rhs);
            self.out.reframe(root, coordinates)
        };
        let content = self.out.edge(root).rhs;
        let mut sigma: HashMap<String, TermId> = HashMap::default();
        let mut contents: Vec<(TermId, TermId)> = vec![(lhs_pattern, content)];
        let mut condition_proofs: Vec<ConditionProof> = vec![];
        for (i, cond) in rewrite.conditions().iter().enumerate() {
            if let Some((var, call)) = cond.binding() {
                let var = var.clone();
                let call = pattern_term(&mut self.out.term_dag, call);
                let cond_names = names
                    .patterns
                    .get(i + 1)
                    .map(|names| names.iter().cloned().collect())
                    .unwrap_or_default();
                let cond_ctx = ExpandCtx {
                    names: cond_names,
                    labels: &labels[i + 1],
                    root_binding: names.classes.get(&var).cloned(),
                    ..ctx.clone()
                };
                let cls_v = match variables.get(&var).copied() {
                    Some(occurrence) => occurrence.cls,
                    None => {
                        let binding = names
                            .classes
                            .get(&var)
                            .ok_or_else(|| format!("no class binding for {var}"))?;
                        let class = self.sub(&match_subst, binding)?;
                        variables.insert(
                            var.clone(),
                            Occurrence {
                                cls: class,
                                row: None,
                                support: self.optional_support(&match_prems, class)?,
                            },
                        );
                        class
                    }
                };
                let pattern = match self.out.term_dag.get(call) {
                    Term::Var(name) => rewrite.globals.get(name).copied().unwrap_or(call),
                    _ => call,
                };
                let Expansion {
                    proof: p,
                    variables: expanded,
                    occurrences: occ_v,
                    slots,
                } = self.expand(cls_v, pattern, &[], &cond_ctx, variables)?;
                variables = expanded;
                variables.insert(
                    var.clone(),
                    Occurrence {
                        row: None,
                        ..occ_v[&Vec::new()]
                    },
                );
                let p = self.lift(p, &frame, &slots)?;
                let c_v = self.out.edge(p).rhs;
                contents.push((call, c_v));
                condition_proofs.push(ConditionProof {
                    variable: var,
                    pattern: call,
                    proof: p,
                    occurrences: occ_v,
                });
            }
        }
        // Each class variable is its class under the frame's renaming of it, as
        // the compiler builds the right-hand side; a slot literal is that slot;
        // what the frame does not name is read off the contents.
        for (v, occurrence) in &variables {
            if let Some(r) = frame.ren(v) {
                let m: SlotMap = r.iter().map(|(k, v)| (*k, *v)).collect();
                let d = self.dec(occurrence.cls)?;
                let completion = self.complete(&m, d);
                let s = rename(&mut self.out.term_dag, &completion, d);

                sigma.insert(v.clone(), s);
            }
        }
        let mut literals: Vec<String> = vec![];
        for (pattern, _) in &contents {
            for v in rewrite.pattern_vars(&self.out.term_dag, *pattern) {
                if v.starts_with('$') && !literals.contains(&v) {
                    literals.push(v);
                }
            }
        }
        for v in literals {
            if let Some(r) = frame.ren(&v)
                && let Some(&s) = r.get(&0)
            {
                let term = slot_term(&mut self.out.term_dag, s);
                sigma.insert(v, term);
            }
        }
        for (pattern, content) in contents {
            self.bind_from_content(pattern, content, &mut sigma)?;
        }
        let coordinates = rewrite
            .globals
            .values()
            .flat_map(|&term| all_slots(&self.out.term_dag, term))
            .filter_map(|slot| frame.node_slot("@globals", slot).map(|at| (at, slot)));
        let to_source = Renaming::completing(coordinates).ok_or("non-injective global frame")?;
        for term in sigma.values_mut() {
            *term = rename(&mut self.out.term_dag, &to_source, *term);
        }
        // minted slots: right-hand-side literals the body never mentions
        {
            for v in rewrite.pattern_vars(&self.out.term_dag, rhs_pattern) {
                if !sigma.contains_key(&v) {
                    if !v.starts_with('$') {
                        return Err(format!("{v} occurs only on the right-hand side of {name}"));
                    }
                    let f = self.fresh();
                    sigma.insert(v, slot_term(&mut self.out.term_dag, f));
                }
            }
        }
        let sigma_order: Vec<(String, TermId)> = {
            let mut order = rewrite.pattern_vars(&self.out.term_dag, lhs_pattern);
            for cond in rewrite.conditions() {
                if let Some((var, call)) = cond.binding() {
                    let var = var.clone();
                    let call = pattern_term(&mut self.out.term_dag, call);
                    if !order.contains(&var) {
                        order.push(var.clone());
                    }
                    for v in rewrite.pattern_vars(&self.out.term_dag, call) {
                        if !order.contains(&v) {
                            order.push(v);
                        }
                    }
                }
            }
            {
                for v in rewrite.pattern_vars(&self.out.term_dag, rhs_pattern) {
                    if !order.contains(&v) {
                        order.push(v);
                    }
                }
            }
            order.into_iter().map(|v| (v.clone(), sigma[&v])).collect()
        };
        for (v, s) in &sigma_order {
            log::debug!("rule {name}: {v} := {}", self.out_string(*s));
        }

        let instance_lhs = rewrite.instantiate(&mut self.out.term_dag, lhs_pattern, &sigma)?;
        let instance_lhs = self
            .program
            .refresh_binders(&mut self.out.term_dag, instance_lhs);
        let instance_rhs = rewrite.instantiate(&mut self.out.term_dag, rhs_pattern, &sigma)?;
        let instance_rhs = self
            .program
            .refresh_binders(&mut self.out.term_dag, instance_rhs);
        // the root premise: cls_p = ·L[σ]
        let root = self
            .fit(root, instance_lhs, &root_occ)
            .map_err(|e| format!("root of {name}: {e}"))?;
        let mut premises = vec![root];
        for ConditionProof {
            variable: var,
            pattern: call,
            proof: p,
            occurrences: occ_v,
        } in condition_proofs
        {
            let call_inst = rewrite.instantiate(&mut self.out.term_dag, call, &sigma)?;
            let call_inst = self
                .program
                .refresh_binders(&mut self.out.term_dag, call_inst);
            let p = self
                .fit(p, call_inst, &occ_v)
                .map_err(|e| format!("condition {var} of {name}: {e}"))?; // dec(cls_v) = ·call[σ]
            // from the class to σ(v), a renaming of it
            let d = self.dec(variables[&var].cls)?;
            let target = sigma[&var];
            let mut pairs = BTreeMap::new();
            self.unify_slots(d, target, &mut pairs)
                .map_err(|e| format!("σ({var}) is not a renaming of its class: {e}"))?;
            let rho =
                Renaming::completing(pairs.into_iter()).ok_or("non-injective class renaming")?;
            let p = self.rename_both(p, &rho); // σ(v) = ·call[σ]
            let p = self
                .fit_content(p, call_inst, &occ_v)
                .map_err(|e| format!("condition {var} of {name}: {e}"))?;
            premises.push(p);
        }
        let rule_step = self.out.rule(
            Proposition::new(instance_lhs, instance_rhs),
            name.to_string(),
            sigma_order,
            premises,
            self.program,
        );
        self.note(rule_step);
        let p = self.trans(root, rule_step)?; // cls_p = ·R[σ]
        Ok(RuleInstance {
            proof: p,
            head: rule_step,
            origin: self.sub(subst, root_class)?,
            occurrences: self.pattern_occurrences(rhs_pattern, &variables),
        })
    }

    /// The classes at a right-hand-side pattern's variable positions.
    fn pattern_occurrences(
        &self,
        pattern: TermId,
        variables: &HashMap<String, Occurrence>,
    ) -> HashMap<Vec<usize>, Occurrence> {
        let mut occurrences = HashMap::default();
        let mut pending = vec![(pattern, Vec::new())];
        while let Some((term, path)) = pending.pop() {
            match self.out.term_dag.get(term) {
                Term::Var(variable) => {
                    if let Some(&occurrence) = variables.get(variable) {
                        occurrences.insert(path, occurrence);
                    }
                }
                Term::App(_, children) => {
                    for (index, &child) in children.iter().enumerate() {
                        let mut path = path.clone();
                        path.push(index);
                        pending.push((child, path));
                    }
                }
                Term::Lit(_) => {}
            }
        }
        occurrences
    }

    pub(super) fn atom_label(
        &self,
        labels: &BTreeMap<String, Option<String>>,
        var: &str,
    ) -> Option<String> {
        labels.get(var).and_then(Clone::clone)
    }

    /// Restate the expanded pattern in its frame coordinates. Slots identified
    /// by the frame share one representative; the remaining occurrence slots
    /// get fresh names and are related by their recorded support certificates.
    pub(super) fn lift(
        &mut self,
        proof: ViewId,
        frame: &Fr,
        nodes: &[(String, i64, i64)],
    ) -> LiftResult<ViewId> {
        let renaming = self.out.edge(proof).renaming.clone();
        let proof = self.content_form(proof);
        let content = self.out.edge(proof).rhs;
        let slots = all_slots(&self.out.term_dag, content);
        let mut pairs = BTreeMap::new();
        let mut taken = BTreeSet::new();
        for (atom, node, slot) in nodes {
            let slot = renaming.apply(*slot);
            let Some(target) = frame.node_slot(atom, *node) else {
                continue;
            };
            if slots.contains(&slot) && !pairs.contains_key(&slot) && taken.insert(target) {
                pairs.insert(slot, target);
            }
        }
        self.fresh.reserve(taken);
        for slot in slots {
            pairs.entry(slot).or_insert_with(|| self.fresh());
        }
        let coordinates =
            Renaming::completing(pairs).ok_or("recorded atom coordinates are not injective")?;
        let proof = self.out.reframe(proof, coordinates);
        Ok(self.note(proof))
    }

    /// Read a substitution off a pattern's instance: each variable's first
    /// occurrence binds it, a slot literal binds to the slot at its position.
    pub(super) fn bind_from_content(
        &mut self,
        pattern: TermId,
        content: TermId,
        sigma: &mut HashMap<String, TermId>,
    ) -> LiftResult<()> {
        match self.out.term_dag.get(pattern).clone() {
            Term::Var(v) => {
                if sigma.contains_key(&v) {
                    // another occurrence may read the class through a symmetry or
                    // spell a redundant slot otherwise; the first occurrence stands
                    return Ok(());
                }
                if v.starts_with('$')
                    && super::super::terms::slot_of(&self.out.term_dag, content).is_none()
                {
                    return Err(format!(
                        "literal {v} stands at a non-slot {}",
                        self.out_string(content)
                    ));
                }
                sigma.insert(v, content);
                Ok(())
            }
            Term::Lit(_) => Ok(()),
            Term::App(head, kids) => {
                let Term::App(_, ckids) = self.out.term_dag.get(content).clone() else {
                    return Err(format!(
                        "pattern {} met a non-application {}",
                        self.out_string(pattern),
                        self.out_string(content)
                    ));
                };
                if kids.len() != ckids.len() {
                    return Err("pattern and instance differ in arity".into());
                }
                for (i, (k, c)) in kids.iter().zip(ckids.iter()).enumerate() {
                    if matches!(
                        self.program.constructors[&head].columns[i],
                        ColumnKind::Payload(_)
                    ) && let Term::Var(var) = self.out.term_dag.get(*k)
                    {
                        sigma.entry(var.clone()).or_insert(*c);
                    } else {
                        self.bind_from_content(*k, *c, sigma)?;
                    }
                }
                Ok(())
            }
        }
    }
}
