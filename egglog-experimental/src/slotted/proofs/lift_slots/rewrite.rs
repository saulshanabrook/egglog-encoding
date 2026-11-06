//! Instantiate source rewrites from encoded matches.

use super::*;

struct ConditionProof {
    variable: String,
    pattern: TermId,
    proof: ViewId,
    occurrences: HashMap<Vec<usize>, Occurrence>,
}

impl SlotLifter<'_> {
    pub(super) fn apply_rule(
        &mut self,
        name: &str,
        prems: &[ProofId],
        subst: &IndexMap<String, TermId>,
        lhs: TermId,
        rhs: TermId,
    ) -> LiftResult<ViewId> {
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
        let bridges: HashMap<TermId, ProofId> = rekeys.into_iter().collect();
        let frame = {
            let m = self.sub(subst, &names.frame)?;
            frame_from_term(self.egg(), m).ok_or("the apply rule's frame is not a frame")?
        };
        // Expand the matched atoms along the patterns, recording each variable's
        // class as the rows show it; the substitution is then read off the
        // expansions' contents, lifted into the frame's slot names.
        let cls_p = self.sub(&match_subst, root_class)?;
        let ctx = ExpandCtx {
            prems: &match_prems,
            subst: &match_subst,
            names: names.patterns[0].iter().cloned().collect(),
            classes: names.classes.clone(),
            readings: names.readings.clone(),
            bridges: &bridges,
        };
        let Expansion {
            proof: root,
            mut variables,
            occurrences: root_occ,
        } = self.expand(cls_p, lhs_pattern, &[], &ctx, HashMap::default())?;
        let root = self.content_form(root); // cls_p = C
        let root_atom = self
            .atom_label(&frame, &root_name, lhs_pattern, root_occ.get(&vec![]))
            .or(Some("@atom:0".to_string()));
        let nested = self.nested_node_slots(
            &frame,
            lhs_pattern,
            &root_occ,
            &ctx.names,
            self.out.edge(root).rhs,
        )?;
        let (root, _) = self.lift(root, &frame, root_atom.as_deref(), &nested);
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
                    ..ctx.clone()
                };
                let cls_v = match variables.get(&var).copied() {
                    Some(c) => c,
                    None => {
                        let binding = names
                            .classes
                            .get(&var)
                            .ok_or_else(|| format!("no class binding for {var}"))?;
                        let class = self.sub(&match_subst, binding)?;
                        variables.insert(var.clone(), class);
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
                } = self.expand(cls_v, pattern, &[], &cond_ctx, variables)?;
                variables = expanded;
                let p = self.content_form(p); // cls_v = C_v
                let atom = self.atom_label(&frame, &var, call, occ_v.get(&vec![]));
                let nested = self.nested_node_slots(
                    &frame,
                    call,
                    &occ_v,
                    &cond_ctx.names,
                    self.out.edge(p).rhs,
                )?;
                let (p, _) = self.lift(p, &frame, atom.as_deref(), &nested);
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
        for (v, &cls) in &variables {
            if let Some(r) = frame.ren(v) {
                let m: SlotMap = r.iter().map(|(k, v)| (*k, *v)).collect();
                let d = self.dec(cls)?;
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
            let d = self.dec(variables[&var])?;
            let target = sigma[&var];
            let mut pairs = BTreeMap::new();
            self.unify_slots(d, target, &mut pairs)
                .map_err(|e| format!("σ({var}) is not a renaming of its class: {e}"))?;
            let rho =
                Renaming::completing(pairs.into_iter()).ok_or("non-injective class renaming")?;
            let p = self.rename_both(p, &rho); // σ(v) = ·call[σ]
            let p = self.fit_content(p, call_inst, &occ_v)?;
            premises.push(p);
        }
        let rule_step = self.out.rule(
            Proposition::new(instance_lhs, instance_rhs),
            name.to_string(),
            sigma_order.clone(),
            premises.clone(),
            self.program,
        );
        self.note(rule_step);
        let p = self.trans(root, rule_step)?; // cls_p = ·R[σ]
        if lhs == rhs && self.is_carrier_term(lhs) {
            // the step states the reflexivity of a term the head built: a
            // subterm of the instance, which the rule may conclude
            let built = self.dec(lhs)?;
            let found = self
                .find_subterm_like(instance_rhs, built)
                .or(self.find_subterm_like(instance_lhs, built));
            if let Some(sub) = found {
                let refl = self.out.rule(
                    Proposition::new(sub, sub),
                    name.to_string(),
                    sigma_order,
                    premises,
                    self.program,
                );
                let refl = self.note(refl);
                let reframed = self.align(refl, built)?; // sub = ·built
                let s = self.out.sym(reframed); // built = ·sub
                return self.trans(s, reframed);
            }
        }
        if !self.is_carrier_term(lhs) {
            // a bare-variable right-hand side states an `Equated` row: cls_p = ·cls_x
            let (_, _, cls_x) = self.row_sides(lhs)?;
            let target = self.dec(cls_x)?;
            return self.align(p, target);
        }
        // the built term, which the instance may spell with other names for the
        // slots the class does not depend on
        let origin = self.sub(subst, root_class)?;
        let built = if lhs == rhs {
            lhs
        } else if lhs == origin {
            rhs
        } else if rhs == origin {
            lhs
        } else {
            return Err("the step relates neither side with the matched class".into());
        };
        let target = self.dec(built)?;
        let rhs_occ = self.pattern_occurrences(rhs_pattern, &variables);
        let p = self
            .fit(p, target, &rhs_occ)
            .map_err(|e| format!("result of {name}: {e}"))?;
        self.orient(p, lhs, rhs)
    }

    /// The classes at a right-hand-side pattern's variable positions.
    fn pattern_occurrences(
        &self,
        pattern: TermId,
        variables: &HashMap<String, TermId>,
    ) -> HashMap<Vec<usize>, Occurrence> {
        match self.out.term_dag.get(pattern) {
            Term::Var(v) => variables
                .get(v)
                .map(|&cls| (vec![], Occurrence { cls, row: None }))
                .into_iter()
                .collect(),
            Term::App(_, kids) => kids
                .iter()
                .enumerate()
                .flat_map(|(j, &kid)| {
                    self.pattern_occurrences(kid, variables).into_iter().map(
                        move |(path, occurrence)| {
                            (std::iter::once(j).chain(path).collect(), occurrence)
                        },
                    )
                })
                .collect(),
            Term::Lit(_) => HashMap::default(),
        }
    }

    /// The label of the atom whose root is `var`, matched at the row the
    /// expansion found for `pattern`: through the root variable's class slots, or
    /// through a child variable's or literal's, which share a block with the
    /// atom's node slots.
    fn atom_label(
        &self,
        frame: &Fr,
        var: &str,
        pattern: TermId,
        occ: Option<&Occurrence>,
    ) -> Option<String> {
        if let Some(a) = frame.atom_of(var) {
            return Some(a);
        }
        let Some(Occurrence {
            row: Some((row, _)),
            ..
        }) = occ
        else {
            return None;
        };
        let Term::App(head, kids) = self.out.term_dag.get(pattern).clone() else {
            return None;
        };
        let (_, args) = self.app(*row)?;
        let ctor = self.program.constructors.get(&head)?;
        let mut i = 0;
        let mut candidates: Option<BTreeSet<String>> = None;
        for (j, col) in ctor.columns.iter().enumerate() {
            match col {
                ColumnKind::Child | ColumnKind::Var | ColumnKind::Binder => {
                    if let Term::Var(v) = self.out.term_dag.get(kids[j]) {
                        let edge = renaming_from_term(self.egg(), args[i]);
                        if let Some(edge) = edge {
                            for (t, s) in edge.iter() {
                                let found: BTreeSet<String> =
                                    if matches!(col, ColumnKind::Var | ColumnKind::Binder) {
                                        frame.node_atoms_with_literal(v, *s).into_iter().collect()
                                    } else {
                                        frame.node_atoms_with(v, *t, *s).into_iter().collect()
                                    };
                                if found.is_empty() {
                                    continue;
                                }
                                candidates = Some(match candidates {
                                    None => found,
                                    Some(c) => c.intersection(&found).cloned().collect(),
                                });
                            }
                        }
                    }
                    i += if *col == ColumnKind::Child { 2 } else { 1 };
                }
                ColumnKind::Payload(_) => i += 1,
            }
        }
        candidates.and_then(|c| c.into_iter().next())
    }

    /// The frame coordinates of the nested atoms' node slots, as `(content slot,
    /// frame slot)` pairs: a nested row's node slot reaches the content through
    /// the renaming its occurrence spells it with.
    fn nested_node_slots(
        &mut self,
        frame: &Fr,
        pattern: TermId,
        occ: &HashMap<Vec<usize>, Occurrence>,
        names: &HashMap<Vec<usize>, String>,
        content: TermId,
    ) -> LiftResult<Vec<(i64, i64)>> {
        let mut out = vec![];
        let mut paths: Vec<&Vec<usize>> = occ.keys().filter(|p| !p.is_empty()).collect();
        paths.sort();
        for path in paths {
            let o = occ[path];
            let Some((row, _)) = o.row else { continue };
            let Some(name) = names.get(path) else {
                continue;
            };
            let sub_pattern = self.subterm_at(pattern, path)?;
            let Some(label) = self.atom_label(frame, name, sub_pattern, Some(&o)) else {
                continue;
            };
            let dr = self.dec(row)?;
            let sub = self.subterm_at(content, path)?;
            let mut pairs = BTreeMap::new();
            if self.unify_slots(dr, sub, &mut pairs).is_err() {
                continue;
            }
            for (s, cs) in pairs {
                if let Some(f) = frame.node_slot(&label, s) {
                    out.push((cs, f));
                }
            }
        }
        Ok(out)
    }

    /// A content in a matched node's own slot names restated in the frame's: each
    /// node slot goes to the pattern slot the frame gave it (the root atom's
    /// through `atom`, the nested atoms' as `nested` lists them), the rest (slots
    /// the pattern never named) to fresh names. Where two content slots would
    /// take one frame name, only the first does: a redundancy certificate is
    /// needed for the other.
    pub(super) fn lift(
        &mut self,
        p: ViewId,
        frame: &Fr,
        atom: Option<&str>,
        nested: &[(i64, i64)],
    ) -> (ViewId, Renaming) {
        let content = self.out.edge(p).rhs;
        let slots = all_slots(&self.out.term_dag, content);
        let mut pairs: Vec<(i64, i64)> = vec![];
        let mut taken: BTreeSet<i64> = BTreeSet::new();
        for s in &slots {
            if let Some(a) = atom
                && let Some(f) = frame.node_slot(a, *s)
            {
                pairs.push((*s, f));
                taken.insert(f);
            }
        }
        for (cs, f) in nested {
            if !slots.contains(cs) || pairs.iter().any(|(k, _)| k == cs) || taken.contains(f) {
                continue;
            }
            pairs.push((*cs, *f));
            taken.insert(*f);
        }
        self.fresh.reserve(taken);
        for s in &slots {
            if !pairs.iter().any(|(k, _)| k == s) {
                let f = self.fresh();
                pairs.push((*s, f));
            }
        }
        let Some(pi) = Renaming::completing(pairs) else {
            return (p, Renaming::identity());
        };
        let r = self.out.reframe(p, pi.clone());
        (self.note(r), pi)
    }

    /// Read a substitution off a pattern's instance: each variable's first
    /// occurrence binds it, a slot literal binds to the slot at its position.
    fn bind_from_content(
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

    /// A subterm of `haystack` that is `needle` up to a bijection of slots.
    fn find_subterm_like(&self, haystack: TermId, needle: TermId) -> Option<TermId> {
        let mut stack = vec![haystack];
        while let Some(t) = stack.pop() {
            let mut pairs = BTreeMap::new();
            if self.unify_slots(t, needle, &mut pairs).is_ok()
                && Renaming::completing(pairs.into_iter()).is_some()
            {
                return Some(t);
            }
            if let Term::App(_, kids) = self.out.term_dag.get(t) {
                stack.extend(kids.iter().copied());
            }
        }
        None
    }
}
