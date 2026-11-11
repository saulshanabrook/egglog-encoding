//! Recover source patterns and bindings from match premises.

use super::*;

impl SlotLifter<'_, NativeProofs<'_>> {
    pub(super) fn selected_readings(
        &self,
        matched: ProofId,
        applied_name: Option<&str>,
        applied: &IndexMap<String, TermId>,
    ) -> LiftResult<Vec<crate::slotted::runtime::SelectedReading>> {
        use egglog::ast::{ResolvedExpr, ResolvedFact};
        let Justification::Rule {
            name, substitution, ..
        } = self.egg.get(matched).justification()
        else {
            return Err("frame refinement lacks its match rule".into());
        };
        let matched = self.native_rule_named(name)?;
        let Some((binding, expression)) = matched.body.iter().find_map(|fact| {
            let ResolvedFact::Eq(
                _,
                ResolvedExpr::Var(_, output),
                ResolvedExpr::Call(_, primitive, args),
            ) = fact
            else {
                return None;
            };
            (primitive.name() == "refinements").then(|| (output.name.as_str(), &args[0]))
        }) else {
            return Ok(vec![]);
        };
        fn frame(
            egg: &TermDag,
            expression: &ResolvedExpr,
            values: &IndexMap<String, TermId>,
        ) -> Option<Fr> {
            match expression {
                ResolvedExpr::Var(_, variable) => {
                    frame_from_term(egg, *values.get(&variable.name)?)
                }
                ResolvedExpr::Call(_, primitive, args) if primitive.name() == "anchor" => {
                    let [base, ResolvedExpr::Lit(_, Literal::String(name))] = args.as_slice()
                    else {
                        return None;
                    };
                    Some(Fr::new(frame(egg, base, values)?.anchored(name)?))
                }
                _ => None,
            }
        }
        fn choice<'a>(expression: &'a ResolvedExpr, binding: &str) -> Option<&'a ResolvedExpr> {
            let ResolvedExpr::Call(_, primitive, args) = expression else {
                return None;
            };
            if primitive.name() == "vec-get"
                && matches!(&args[0], ResolvedExpr::Var(_, variable) if variable.name == binding)
            {
                return args.get(1);
            }
            args.iter().find_map(|arg| choice(arg, binding))
        }
        let applied_rule = self.native_rule_named(applied_name.unwrap_or(name))?;
        let index = applied_rule
            .body
            .iter()
            .flat_map(SourceFact::terms)
            .find_map(|expression| choice(expression, binding))
            .ok_or("refinement has no recorded element read")?;
        let index = match index {
            ResolvedExpr::Var(_, variable) => self.egg().get(self.sub(applied, &variable.name)?),
            _ => return Err("refinement choice is not a bound value".into()),
        };
        let Term::Lit(Literal::Int(index)) = index else {
            return Err("recorded refinement choice is not an integer".into());
        };
        let input = frame(self.egg(), expression, substitution)
            .ok_or("recorded refinement input is not a frame")?;
        input
            .refinement_readings(usize::try_from(*index).map_err(|_| "negative refinement choice")?)
            .ok_or_else(|| "recorded refinement choice is out of range".into())
    }

    /// The equality denoted by one side of a row proof's proposition. A row proof
    /// may relate a row to its re-keyed form, or state a row reflexively through
    /// a composition; the consumer wants the equality of the row as it reads it.
    pub(super) fn row_eq(&mut self, id: ProofId, rhs_side: bool) -> LiftResult<ViewId> {
        let proof = self.egg.get(id).clone();
        match proof.justification() {
            Justification::Sym(x) => {
                let x = *x;
                self.row_eq(x, !rhs_side)
            }
            Justification::Trans(a, b) => {
                let (a, b) = (*a, *b);
                if rhs_side {
                    self.row_eq(b, true)
                } else {
                    self.row_eq(a, false)
                }
            }
            Justification::Congr { proof: base, .. } if !rhs_side => {
                let base = *base;
                self.row_eq(base, false)
            }
            _ => self.eq_direct(id),
        }
    }

    /// A stored match's proof unwrapped to the rule firing that wrote the row,
    /// with the proofs that re-keyed its class columns since: `(old, old = new)`.
    pub(super) fn unwrap_match(
        &self,
        proof: ProofId,
    ) -> LiftResult<(ProofId, Vec<(TermId, ProofId)>)> {
        self.match_side(proof, true)
    }

    fn match_side(
        &self,
        proof: ProofId,
        rhs: bool,
    ) -> LiftResult<(ProofId, Vec<(TermId, ProofId)>)> {
        let p = self.egg.get(proof);
        match p.justification() {
            Justification::Rule { .. } => Ok((proof, vec![])),
            Justification::Congr {
                proof: base,
                child_index,
                child_proof,
            } => {
                if !rhs {
                    return self.match_side(*base, false);
                }
                let (firing, mut bridges) = self.match_side(*base, true)?;
                // the re-keyed column's old class is in the base row
                let base_row = self.egg.get(*base).rhs();
                let old = self
                    .app(base_row)
                    .and_then(|(_, a)| a.get(*child_index).copied())
                    .unwrap_or(self.egg.get(*child_proof).lhs());
                let child = self.egg.get(*child_proof);
                if child.lhs() != child.rhs() {
                    bridges.push((old, *child_proof));
                }
                Ok((firing, bridges))
            }
            Justification::Trans(a, b) => self.match_side(if rhs { *b } else { *a }, rhs),
            Justification::Sym(a) => self.match_side(*a, !rhs),
            other => Err(format!("a stored match justified by {other:?}")),
        }
    }

    /// A re-key's child proof as `old = ·new`, whichever way it was stated.
    fn bridge_eq(&mut self, bridge: ProofId, old: TermId) -> LiftResult<(ViewId, TermId)> {
        let pr = self.egg.get(bridge);
        let (l, r) = (pr.lhs(), pr.rhs());
        let e = self.eq(bridge)?;
        if l == old {
            Ok((e, r))
        } else if r == old {
            let s = self.out.sym(e);
            Ok((self.note(s), l))
        } else {
            Err(format!(
                "re-key {} relates neither side with {}",
                self.prop_string(e),
                self.egg_string(old)
            ))
        }
    }

    /// `dec(cls) = ·T`, expanding the pattern's recorded constructor premises
    /// through the readings selected by the match.
    pub(super) fn expand(
        &mut self,
        cls: TermId,
        pattern: TermId,
        path: &[usize],
        ctx: &ExpandCtx<'_>,
        variables: HashMap<String, Occurrence>,
    ) -> LiftResult<Expansion> {
        let cls = match self.atom_premise(path, ctx)? {
            Some((proof, _)) => self.egg.get(proof).lhs(),
            None => cls,
        };
        let mut expanded = self.expand_old(cls, pattern, path, ctx, variables)?;
        // A flattened atom retains the symmetry selected for this occurrence.
        if let Some(name) = ctx.names.get(path)
            && let Some(reading) = ctx.readings.get(name)
        {
            let g = self.sub(ctx.subst, reading)?;
            let g = self.slot_map(g)?;
            let reading = self.reading_proof(cls, &g, ctx.prems)?;
            let symmetry = self.symmetry(cls, &g, reading)?;
            let completion = Renaming::completing(g.iter().map(|(k, v)| (*k, *v)))
                .ok_or("reading is not injective")?;
            let renamed = self.rename_both(expanded.proof, &completion);
            let symmetry = self.out.reframe(symmetry, completion);
            let symmetry = self.note(symmetry);
            expanded.proof = self.trans(symmetry, renamed)?;
        }
        // the class may have been re-keyed since the firing, perhaps more than
        // once: state it from the class it became
        let mut current = cls;
        let mut support = expanded.occurrences[path].support;
        while let Some(&bridge) = ctx.bridges.get(&current) {
            let (e, new) = self.bridge_eq(bridge, current)?; // old = ·new
            let s = self.out.sym(e);
            expanded.proof = self.trans(s, expanded.proof)?;
            if let Some(previous) = support {
                support = Some(self.transport_support(previous, s)?);
            }
            current = new;
        }
        let occurrence = expanded
            .occurrences
            .get_mut(path)
            .ok_or("missing expanded occurrence")?;
        occurrence.cls = current;
        occurrence.support = support;
        if let Some((_, proof)) = &mut occurrence.row {
            *proof = expanded.proof;
        }
        if let Term::Var(variable) = self.out.term_dag.get(pattern)
            && !variable.starts_with('$')
        {
            // The apply frame describes the current class; retain its actual
            // input support transported through the same recorded equalities.
            expanded.variables.insert(variable.clone(), *occurrence);
        }
        Ok(expanded)
    }

    fn expand_old(
        &mut self,
        cls: TermId,
        pattern: TermId,
        path: &[usize],
        ctx: &ExpandCtx<'_>,
        mut variables: HashMap<String, Occurrence>,
    ) -> LiftResult<Expansion> {
        let support = self.optional_support(ctx.prems, cls)?;
        let mut occurrences = HashMap::from_iter([(
            path.to_vec(),
            Occurrence {
                cls,
                row: None,
                support,
            },
        )]);
        let Term::App(ctor, kids) = self.out.term_dag.get(pattern).clone() else {
            if let Term::Var(v) = self.out.term_dag.get(pattern)
                && !v.starts_with('$')
            {
                variables.insert(v.clone(), occurrences[path]);
            }
            let support = self.support_premise(ctx.prems, cls)?;
            let proof = self.support_class(support, true)?;
            return Ok(Expansion {
                proof,
                variables,
                occurrences,
                slots: vec![],
            });
        };
        let prems = ctx.prems;
        if !ctx.names.contains_key(path)
            && super::super::terms::pattern_vars(&self.out.term_dag, pattern)
                .iter()
                .all(|v| v.starts_with('$'))
        {
            let premise = self.global_premise(ctx)?;
            let row = self.egg.get(premise).rhs();
            let (_, args) = self.app(row).ok_or("global premise is not a leader edge")?;
            let source = args[0];
            let decoded = self.dec(source)?;
            if !self
                .program
                .alpha_eq(&mut self.out.term_dag, decoded, pattern)
            {
                return Err(format!(
                    "recorded global premise {premise} has a different source spelling"
                ));
            }
            let proof = self.eq(premise)?;
            let row_eq = self.out.sym(proof);
            let proof = self.align(row_eq, pattern)?;
            occurrences.insert(
                path.to_vec(),
                Occurrence {
                    cls,
                    row: Some((source, row_eq)),
                    support,
                },
            );
            return Ok(Expansion {
                proof,
                variables,
                occurrences,
                slots: vec![],
            });
        }
        let columns = self
            .program
            .constructors
            .get(&ctor)
            .ok_or_else(|| format!("unknown constructor {ctor}"))?
            .columns
            .clone();
        let (atom, fact_index) = self
            .atom_premise(path, ctx)?
            .ok_or("constructor pattern lacks its recorded atom")?;
        let native_rule = self.native_rule(ctx.firing)?;
        let egglog::ast::ResolvedFact::Eq(_, _, egglog::ast::ResolvedExpr::Call(_, _, arguments)) =
            &native_rule.body[fact_index]
        else {
            unreachable!("atom_premise selects a constructor fact")
        };
        let bindings: Vec<_> = self.program.constructors[&ctor]
            .encoded_columns()
            .map(|(_, kind, physical)| {
                if *kind != ColumnKind::Child {
                    return None;
                }
                match &arguments[physical.end - 1] {
                    egglog::ast::ResolvedExpr::Var(_, variable) => Some(variable.name.clone()),
                    _ => None,
                }
            })
            .collect();
        let mut p = self.eq(atom)?;
        let row = self.egg.get(atom).rhs();
        log::debug!(
            "expand {} at {path:?}: row {}",
            self.egg_string(cls),
            self.egg_string(row)
        );
        occurrences.insert(
            path.to_vec(),
            Occurrence {
                cls,
                row: Some((row, p)),
                support,
            },
        );
        let label = ctx
            .names
            .get(path)
            .and_then(|name| self.atom_label(ctx.labels, name));
        let mut slots = Vec::new();
        let (_, args) = self.app(row).ok_or("not a row")?;
        if let Some(label) = &label {
            for (column, kind, physical) in self.program.constructors[&ctor].encoded_columns() {
                if matches!(kind, ColumnKind::Payload(_)) {
                    continue;
                }
                let edge = self.slot_map(args[physical.start])?;
                for (child, node) in edge {
                    let content = match kind {
                        ColumnKind::Var => node,
                        ColumnKind::Binder | ColumnKind::Child => {
                            self.edge_memo[&(row, column)].apply(child)
                        }
                        ColumnKind::Payload(_) => unreachable!(),
                    };
                    slots.push((label.clone(), node, content));
                }
            }
        }
        let mut i = 0;
        for (j, col) in columns.iter().enumerate() {
            match col {
                ColumnKind::Child => {
                    let child = args[i + 1];
                    i += 2;
                    let kid = kids[j];
                    if let Term::Var(v) = self.out.term_dag.get(kid).clone()
                        && !v.starts_with('$')
                    {
                        let mut current = child;
                        let mut support = self.optional_support(ctx.prems, child)?;
                        let edge = self.slot_map(args[i - 2])?;
                        let selected = ctx.selected.iter().find(|reading| {
                            Some(reading.atom.as_str()) == label.as_deref()
                                && reading.variable == v
                                && reading.edge == edge
                        });
                        let mut bridged = if let Some(reading) = selected {
                            let group = self.group_premise(prems, child)?;
                            let symmetry = self.symmetry(child, &reading.element, group)?;
                            Some(self.out.sym(symmetry))
                        } else {
                            None
                        };
                        while let Some(&bridge) = ctx.bridges.get(&current) {
                            let (e, new) = self.bridge_eq(bridge, current)?; // old = ·new
                            if let Some(previous) = support {
                                let back = self.out.sym(e);
                                support = Some(self.transport_support(previous, back)?);
                            }
                            bridged = Some(match bridged {
                                None => e,
                                Some(prev) => self.trans(prev, e)?,
                            });
                            current = new;
                        }
                        if let Some(e) = bridged {
                            let completion = self.edge_memo[&(row, j)].clone();
                            let renamed = self.rename_both(e, &completion);
                            p = self.out.congr(p, j, renamed).map_err(|e| e.to_string())?;
                            p = self.note(p);
                        }
                        let occurrence = Occurrence {
                            cls: current,
                            row: None,
                            support,
                        };
                        variables.entry(v).or_insert(occurrence);
                        let mut sub_path = path.to_vec();
                        sub_path.push(j);
                        occurrences.insert(sub_path, occurrence);
                    }
                    if matches!(self.out.term_dag.get(kid), Term::App(..)) {
                        let mut sub_path = path.to_vec();
                        sub_path.push(j);
                        let child_ctx = ExpandCtx {
                            root_binding: bindings[j].clone(),
                            ..ctx.clone()
                        };
                        let Expansion {
                            proof: sub,
                            variables: expanded,
                            occurrences: nested,
                            slots: nested_slots,
                        } = self.expand(child, kid, &sub_path, &child_ctx, variables)?;
                        variables = expanded;
                        occurrences.extend(nested);
                        let completion = self.edge_memo[&(row, j)].clone();
                        let embedding = completion.compose(&self.out.edge(sub).renaming);
                        slots.extend(
                            nested_slots.into_iter().map(|(atom, node, content)| {
                                (atom, node, embedding.apply(content))
                            }),
                        );
                        let renamed = self.rename_both(sub, &completion);
                        p = self.out.congr(p, j, renamed).map_err(|e| e.to_string())?;
                        p = self.note(p);
                    }
                }
                ColumnKind::Var | ColumnKind::Binder => i += 1,
                ColumnKind::Payload(_) => i += 1,
            }
        }
        Ok(Expansion {
            proof: p,
            variables,
            occurrences,
            slots,
        })
    }

    fn native_rule(&self, firing: ProofId) -> LiftResult<&egglog::ast::ResolvedRule> {
        let Justification::Rule { name, .. } = self.egg.get(firing).justification() else {
            return Err("match input lacks its rule firing".into());
        };
        self.native_rule_named(name)
    }

    pub(super) fn native_rule_named(&self, name: &str) -> LiftResult<&egglog::ast::ResolvedRule> {
        self.egg
            .program
            .iter()
            .find_map(|command| match command {
                egglog::ast::ResolvedNCommand::NormRule { rule } if rule.name == name => Some(rule),
                _ => None,
            })
            .ok_or_else(|| format!("match input lacks its original native rule {name}"))
    }

    /// Repeated reads of one function key must carry the same recorded value.
    pub(super) fn function_premise(
        &self,
        premises: &[ProofId],
        prefix: &str,
        class: TermId,
    ) -> LiftResult<Option<ProofId>> {
        let mut selected = None;
        for &proof in premises {
            let row = self.egg.get(proof).rhs();
            if self.app(row).is_some_and(|(head, arguments)| {
                head.starts_with(prefix) && arguments.first() == Some(&class)
            }) {
                if let Some(previous) = selected
                    && self.egg.get(previous).rhs() != row
                {
                    return Err(format!(
                        "{prefix} premises disagree on the value for class {class}"
                    ));
                }
                selected = Some(proof);
            }
        }
        Ok(selected)
    }

    fn global_premise(&self, ctx: &ExpandCtx<'_>) -> LiftResult<ProofId> {
        use egglog::ast::{ResolvedExpr, ResolvedFact};
        let binding = ctx
            .root_binding
            .as_ref()
            .ok_or("global pattern lacks its class binding")?;
        let rule = self.native_rule(ctx.firing)?;
        let index = rule.body.iter().position(|fact| {
            let ResolvedFact::Fact(ResolvedExpr::Call(_, call, arguments)) = fact else { return false; };
            call.name().starts_with("RenamesToLeader_")
                && matches!(arguments.get(2), Some(ResolvedExpr::Var(_, variable)) if &variable.name == binding)
        }).ok_or("global pattern has no recorded leader edge")?;
        ctx.prems
            .get(index)
            .copied()
            .ok_or_else(|| "global premise index is out of range".into())
    }

    fn atom_premise(
        &self,
        path: &[usize],
        ctx: &ExpandCtx<'_>,
    ) -> LiftResult<Option<(ProofId, usize)>> {
        use egglog::ast::{ResolvedExpr, ResolvedFact};
        let Some(label) = ctx
            .names
            .get(path)
            .and_then(|name| ctx.labels.get(name))
            .and_then(Option::as_ref)
        else {
            return Ok(None);
        };
        let rule = self.native_rule(ctx.firing)?;
        let mut row = None;
        for (index, fact) in rule.body.iter().enumerate() {
            let ResolvedFact::Eq(_, _, ResolvedExpr::Call(_, call, arguments)) = fact else {
                continue;
            };
            if self.program.constructors.contains_key(call.name()) {
                row = Some(index);
            }
            if matches!(call.name(), "atom" | "nested-atom")
                && matches!(arguments.first(), Some(ResolvedExpr::Lit(_, Literal::String(value))) if value == label)
            {
                let index = row.ok_or("frame atom has no preceding constructor row")?;
                return ctx
                    .prems
                    .get(index)
                    .copied()
                    .map(|proof| Some((proof, index)))
                    .ok_or_else(|| "constructor premise index is out of range".into());
            }
        }
        Err(format!(
            "match rule {} has no frame atom {label}",
            rule.name
        ))
    }

    /// The selected reading, including any congruences that re-keyed its class.
    fn reading_proof(&self, child: TermId, g: &SlotMap, prems: &[ProofId]) -> LiftResult<ProofId> {
        prems
            .iter()
            .copied()
            .find(|q| {
                let t = self.egg.get(*q).rhs();
                self.app(t).is_some_and(|(h, a)| {
                    h.starts_with("Reading_")
                        && a.len() >= 3
                        && a[0] == child
                        && renaming_from_term(self.egg(), a[2]).as_ref() == Some(g)
                })
            })
            .ok_or_else(|| {
                format!(
                    "no reading row for {} with {}",
                    self.egg_string(child),
                    slot_map_string(g)
                )
            })
    }
}
