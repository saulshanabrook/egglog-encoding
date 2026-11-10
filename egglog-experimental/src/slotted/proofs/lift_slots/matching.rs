//! Recover source patterns and bindings from match premises.

use super::*;

impl SlotLifter<'_> {
    /// Which side of a row proof's proposition a consumer reads.
    fn row_side(&self, proof: ProofId, rhs: bool) -> TermId {
        let p = self.egg.get(proof);
        if rhs { p.rhs() } else { p.lhs() }
    }

    /// The equality denoted by one side of a row proof's proposition. A row proof
    /// may relate a row to its re-keyed form, or state a row reflexively through
    /// a composition; the consumer wants the equality of the row as it reads it.
    pub(super) fn row_eq(&mut self, id: ProofId, rhs_side: bool) -> LiftResult<ViewId> {
        let proof = self.egg.get(id).clone();
        let (lhs, rhs) = (proof.lhs(), proof.rhs());
        if lhs == rhs {
            // a reflexive row: its own justification says how it holds
            return match proof.justification() {
                Justification::Trans(a, b) => {
                    let (a, b) = (*a, *b);
                    match self.egg.get(a).justification() {
                        Justification::Sym(x) => {
                            let x = *x;
                            let want = self.row_side(x, false) == lhs;
                            self.row_eq(x, !want)
                        }
                        _ => self.row_eq(a, true),
                    }
                    .or_else(|_| self.row_eq(b, true))
                }
                Justification::Sym(x) => {
                    let x = *x;
                    self.row_eq(x, false)
                }
                _ => self.eq_direct(id),
            };
        }
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
        let p = self.egg.get(proof);
        match p.justification() {
            Justification::Rule { .. } => Ok((proof, vec![])),
            Justification::Congr {
                proof: base,
                child_index,
                child_proof,
            } => {
                let (firing, mut bridges) = self.unwrap_match(*base)?;
                // the re-keyed column's old class is in the base row
                let base_row = self.egg.get(*base).rhs();
                let old = self
                    .app(base_row)
                    .and_then(|(_, a)| a.get(*child_index).copied())
                    .unwrap_or(self.egg.get(*child_proof).lhs());
                bridges.push((old, *child_proof));
                Ok((firing, bridges))
            }
            Justification::Trans(a, b) => self.unwrap_match(*a).or_else(|_| self.unwrap_match(*b)),
            Justification::Sym(a) => self.unwrap_match(*a),
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

    /// `dec(cls) = ·T` where `T` expands the matched atoms below `cls` along the
    /// pattern they matched: each column whose pattern is a call is replaced by
    /// that call's own atom, found among the premises by its class and head, read
    /// through the symmetry the match chose for it.
    pub(super) fn expand(
        &mut self,
        cls: TermId,
        pattern: TermId,
        path: &[usize],
        ctx: &ExpandCtx<'_>,
        variables: HashMap<String, TermId>,
    ) -> LiftResult<Expansion> {
        let cls = if let Term::App(head, _) = self.out.term_dag.get(pattern) {
            let has_row = |class| {
                ctx.prems.iter().any(|&p| {
                    let p = self.egg.get(p);
                    p.lhs() == class && self.app(p.rhs()).is_some_and(|(h, _)| h == head)
                })
            };
            if has_row(cls) {
                cls
            } else {
                ctx.bridges
                    .keys()
                    .copied()
                    .find(|&old| {
                        if !has_row(old) {
                            return false;
                        }
                        let mut current = old;
                        let mut seen = HashSet::default();
                        while seen.insert(current) {
                            if current == cls {
                                return true;
                            }
                            let Some(&p) = ctx.bridges.get(&current) else {
                                break;
                            };
                            let p = self.egg.get(p);
                            current = if p.lhs() == current { p.rhs() } else { p.lhs() };
                        }
                        false
                    })
                    .unwrap_or(cls)
            }
        } else {
            cls
        };
        let mut expanded = self.expand_old(cls, pattern, path, ctx, variables)?;
        // the class may have been re-keyed since the firing, perhaps more than
        // once: state it from the class it became
        let mut current = cls;
        while let Some(&bridge) = ctx.bridges.get(&current) {
            let (e, new) = self.bridge_eq(bridge, current)?; // old = ·new
            let s = self.out.sym(e);
            expanded.proof = self.trans(s, expanded.proof)?;
            current = new;
        }
        // A flattened atom retains the symmetry selected for this occurrence.
        if let Some(name) = ctx.names.get(path)
            && let Some(reading) = ctx.readings.get(name)
            && let Ok(g) = self.sub(ctx.subst, reading)
        {
            let g = self.slot_map(g)?;
            if !is_identity(&g) {
                let group = self.reading_group_proof(cls, &g, ctx.prems)?;
                let symmetry = self.symmetry(cls, &g, group)?;
                let completion = Renaming::completing(g.iter().map(|(k, v)| (*k, *v)))
                    .ok_or("reading is not injective")?;
                let renamed = self.rename_both(expanded.proof, &completion);
                let symmetry = self.out.reframe(symmetry, completion);
                let symmetry = self.note(symmetry);
                expanded.proof = self.trans(symmetry, renamed)?;
            }
        }
        Ok(expanded)
    }

    fn expand_old(
        &mut self,
        cls: TermId,
        pattern: TermId,
        path: &[usize],
        ctx: &ExpandCtx<'_>,
        mut variables: HashMap<String, TermId>,
    ) -> LiftResult<Expansion> {
        let mut occurrences = HashMap::from_iter([(path.to_vec(), Occurrence { cls, row: None })]);
        let Term::App(ctor, kids) = self.out.term_dag.get(pattern).clone() else {
            if let Term::Var(v) = self.out.term_dag.get(pattern)
                && !v.starts_with('$')
            {
                variables.insert(v.clone(), cls);
            }
            let t = self.dec(cls)?;
            let proof = self.reflexive(t).or_else(|error| {
                // A variable can name a term constructed by an earlier rewrite.
                // Replay its direct match witness before asking for reflexivity.
                let witness = ctx.prems.iter().copied().find(|&id| {
                    let proof = self.egg.get(id);
                    proof.lhs() == cls || proof.rhs() == cls
                });
                let Some(witness) = witness else {
                    return Err(error);
                };
                self.eq(witness)?;
                self.reflexive(t)
            })?;
            return Ok(Expansion {
                proof,
                variables,
                occurrences,
            });
        };
        let prems = ctx.prems;
        if !ctx.names.contains_key(path)
            && super::super::terms::pattern_vars(&self.out.term_dag, pattern)
                .iter()
                .all(|v| v.starts_with('$'))
        {
            for &premise in prems {
                let row = self.egg.get(premise).rhs();
                let Some((head, args)) = self.app(row) else {
                    continue;
                };
                if !row_kind(head).is_edge() || args.len() < 3 || args[2] != cls {
                    continue;
                }
                let node = args[0];
                let sources = std::iter::once((node, None))
                    .chain(self.egg.proofs().filter_map(|(p, proof)| {
                        if proof.rhs() == node && self.is_carrier_term(proof.lhs()) {
                            Some((proof.lhs(), Some((p, false))))
                        } else if proof.lhs() == node && self.is_carrier_term(proof.rhs()) {
                            Some((proof.rhs(), Some((p, true))))
                        } else {
                            None
                        }
                    }))
                    .collect::<Vec<_>>();
                for (source, bridge) in sources {
                    let decoded = self.dec(source)?;
                    if !self
                        .program
                        .alpha_eq(&mut self.out.term_dag, decoded, pattern)
                    {
                        continue;
                    }
                    let mut proof = self.eq(premise)?;
                    if let Some((bridge, reversed)) = bridge {
                        let mut bridge = self.eq(bridge)?;
                        if reversed {
                            bridge = self.out.sym(bridge);
                        }
                        proof = self.trans(bridge, proof)?;
                    }
                    let row_eq = self.out.sym(proof);
                    if let Ok(proof) = self.align(row_eq, pattern) {
                        occurrences.insert(
                            path.to_vec(),
                            Occurrence {
                                cls,
                                row: Some((source, row_eq)),
                            },
                        );
                        self.global_occurrences(source, path, &mut occurrences)?;
                        return Ok(Expansion {
                            proof,
                            variables,
                            occurrences,
                        });
                    }
                }
            }
        }
        if self.is_leaf_pattern(pattern) {
            // a leaf: its class reaches the constructor's own class by an edge,
            // or is that class
            if let Some(link) = self.leaf_edge(cls, pattern, prems) {
                let e = self.eq(link)?; // leader = m·cls
                let s = self.out.sym(e);
                return Ok(Expansion {
                    proof: self.note(s),
                    variables,
                    occurrences,
                });
            }
        }
        let columns = self
            .program
            .constructors
            .get(&ctor)
            .ok_or_else(|| format!("unknown constructor {ctor}"))?
            .columns
            .clone();
        // the atom row: `cls = (ctor ...)` whose pattern-variable columns hold the
        // substitution's classes
        let atom = prems
            .iter()
            .copied()
            .find(|q| {
                let pr = self.egg.get(*q);
                pr.lhs() == cls
                    && self.app(pr.rhs()).is_some_and(|(h, args)| {
                        h == ctor
                            && self.columns_match(args, &columns, &kids, path, ctx, &variables)
                    })
            })
            .ok_or_else(|| {
                let listed: Vec<String> = prems
                    .iter()
                    .map(|q| {
                        let pr = self.egg.get(*q);
                        format!(
                            "{} = {}",
                            self.egg_string(pr.lhs()),
                            self.egg_string(pr.rhs())
                        )
                    })
                    .collect();
                format!(
                    "no matched {ctor} row for {} among the premises:\n  {}",
                    self.egg_string(cls),
                    listed.join("\n  ")
                )
            })?;
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
            },
        );
        let (_, args) = self.app(row).ok_or("not a row")?;
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
                        let mut bridged: Option<ViewId> = None;
                        while let Some(&bridge) = ctx.bridges.get(&current) {
                            let (e, new) = self.bridge_eq(bridge, current)?; // old = ·new
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
                        variables.entry(v).or_insert(current);
                        let mut sub_path = path.to_vec();
                        sub_path.push(j);
                        occurrences.insert(
                            sub_path,
                            Occurrence {
                                cls: current,
                                row: None,
                            },
                        );
                    }
                    if matches!(self.out.term_dag.get(kid), Term::App(..)) {
                        let mut sub_path = path.to_vec();
                        sub_path.push(j);
                        let Expansion {
                            proof: sub,
                            variables: expanded,
                            occurrences: nested,
                        } = self.expand(child, kid, &sub_path, ctx, variables)?;
                        variables = expanded;
                        occurrences.extend(nested);
                        let completion = self.edge_memo[&(row, j)].clone();
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
        })
    }

    /// A pattern the flattener reaches through its class rather than by an atom
    /// of its own: a constructor with no slotted column and no payload variable.
    fn is_leaf_pattern(&self, pattern: TermId) -> bool {
        let Term::App(ctor, kids) = self.out.term_dag.get(pattern) else {
            return false;
        };
        let Some(c) = self.program.constructors.get(ctor) else {
            return false;
        };
        c.columns
            .iter()
            .all(|k| matches!(k, ColumnKind::Payload(_)))
            && kids
                .iter()
                .all(|k| !matches!(self.out.term_dag.get(*k), Term::Var(_)))
    }

    /// A leaf has no atom name. Its edge premise identifies the matched class,
    /// including the literal payloads that distinguish leaves of one constructor.
    fn leaf_edge(&self, cls: TermId, pattern: TermId, prems: &[ProofId]) -> Option<ProofId> {
        let Term::App(ctor, kids) = self.out.term_dag.get(pattern) else {
            return None;
        };
        prems.iter().copied().find(|&id| {
            self.app(self.egg.get(id).rhs())
                .is_some_and(|(head, args)| {
                    row_kind(head).is_edge()
                        && args.len() >= 3
                        && args[2] == cls
                        && self.app(args[0]).is_some_and(|(head, args)| {
                            head == ctor
                                && args.len() == kids.len()
                                && args
                                    .iter()
                                    .zip(kids)
                                    .all(|(&a, &b)| self.egg().get(a) == self.out.term_dag.get(b))
                        })
                })
        })
    }

    // Prefer a proved representative with fewer free slots so certificates can
    // reach a child whose source spelling still includes a redundant slot.

    fn global_occurrence(&mut self, child: TermId) -> LiftResult<Occurrence> {
        if let Some(&occurrence) = self.occurrence_memo.get(&child) {
            return Ok(occurrence);
        }
        let head = self
            .app(child)
            .ok_or("global child is not a constructor")?
            .0;
        let term = self.dec(child)?;
        let mut free = self.program.free_slots(&self.out.term_dag, term).len();
        let mut occurrence = Occurrence {
            cls: child,
            row: None,
        };
        if free == 0 {
            self.occurrence_memo.insert(child, occurrence);
            return Ok(occurrence);
        }
        if self.carrier_index.is_none() {
            let mut index: HashMap<String, Vec<(ProofId, bool)>> = HashMap::default();
            for (id, proof) in self.egg.proofs() {
                if proof.lhs() == proof.rhs()
                    || !self.is_carrier_term(proof.lhs())
                    || !self.is_carrier_term(proof.rhs())
                {
                    continue;
                }
                for (row, reversed) in [(proof.rhs(), false), (proof.lhs(), true)] {
                    let head = self.app(row).unwrap().0;
                    index
                        .entry(head.to_string())
                        .or_default()
                        .push((id, reversed));
                }
            }
            self.carrier_index = Some(index);
        }
        let count = self
            .carrier_index
            .as_ref()
            .unwrap()
            .get(head)
            .map_or(0, Vec::len);
        for at in 0..count {
            let (id, reversed) = self.carrier_index.as_ref().unwrap()[head][at];
            let proof = self.egg.get(id);
            let (row, cls) = if reversed {
                (proof.lhs(), proof.rhs())
            } else {
                (proof.rhs(), proof.lhs())
            };
            let decoded = self.dec(row)?;
            let mut pairs = BTreeMap::new();
            if self.match_slots(decoded, term, &mut pairs).is_err()
                || Renaming::completing(pairs.into_iter()).is_none()
            {
                continue;
            }
            let target = self.dec(cls)?;
            let target_free = self.program.free_slots(&self.out.term_dag, target).len();
            if target_free >= free {
                continue;
            }
            let mut proof = self.eq(id)?;
            if reversed {
                proof = self.out.sym(proof);
            }
            occurrence = Occurrence {
                cls,
                row: Some((row, proof)),
            };
            free = target_free;
            if free == 0 {
                break;
            }
        }
        self.occurrence_memo.insert(child, occurrence);
        Ok(occurrence)
    }

    fn global_occurrences(
        &mut self,
        node: TermId,
        path: &[usize],
        occurrences: &mut HashMap<Vec<usize>, Occurrence>,
    ) -> LiftResult<()> {
        let (head, args) = self.app(node).ok_or("global node is not a constructor")?;
        let Some(constructor) = self.program.constructors.get(head) else {
            return Ok(());
        };
        let mut physical = 0;
        for (column, kind) in constructor.columns.iter().enumerate() {
            match kind {
                ColumnKind::Child => {
                    let child = *args
                        .get(physical + 1)
                        .ok_or("short global constructor row")?;
                    if self
                        .app(child)
                        .is_some_and(|(h, _)| self.program.constructors.contains_key(h))
                    {
                        let mut child_path = path.to_vec();
                        child_path.push(column);
                        occurrences.insert(child_path.clone(), self.global_occurrence(child)?);
                        self.global_occurrences(child, &child_path, occurrences)?;
                    }
                    physical += 2;
                }
                ColumnKind::Var | ColumnKind::Binder => physical += 1,
                ColumnKind::Payload(_) => physical += 1,
            }
        }
        Ok(())
    }

    /// The group row a `Reading` row for `(child, g)` among the premises derives
    /// from.
    fn reading_group_proof(
        &self,
        child: TermId,
        g: &SlotMap,
        prems: &[ProofId],
    ) -> LiftResult<ProofId> {
        let reading = prems
            .iter()
            .copied()
            .find(|q| {
                let t = self.egg.get(*q).lhs();
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
            })?;
        self.group_row_behind(reading)
    }

    /// Do a row's class columns agree with the substitution where the pattern
    /// names a variable?
    fn columns_match(
        &self,
        args: &[TermId],
        columns: &[ColumnKind],
        kids: &[TermId],
        path: &[usize],
        ctx: &ExpandCtx<'_>,
        variables: &HashMap<String, TermId>,
    ) -> bool {
        let mut i = 0;
        for (j, col) in columns.iter().enumerate() {
            match col {
                ColumnKind::Child => {
                    let class = args.get(i + 1).copied();
                    // the class the match bound the nested atom to, when the
                    // substitution names it
                    let mut sub_path = path.to_vec();
                    sub_path.push(j);
                    let bound = ctx
                        .names
                        .get(&sub_path)
                        .and_then(|name| ctx.classes.get(name))
                        .and_then(|class| ctx.subst.get(class))
                        .copied();
                    match self.out.term_dag.get(kids[j]) {
                        Term::Var(v) => {
                            let bound = ctx.classes.get(v).and_then(|c| ctx.subst.get(c));
                            if let Some(&want) = variables.get(v).or(bound)
                                && class != Some(want)
                            {
                                return false;
                            }
                        }
                        Term::App(..) => match bound {
                            Some(want) => {
                                if class != Some(want) {
                                    return false;
                                }
                            }
                            None if self.is_leaf_pattern(kids[j]) => {
                                if class.is_none_or(|cls| {
                                    self.leaf_edge(cls, kids[j], ctx.prems).is_none()
                                }) {
                                    return false;
                                }
                            }
                            None => {}
                        },
                        Term::Lit(_) => {}
                    }
                    i += 2;
                }
                ColumnKind::Var | ColumnKind::Binder => i += 1,
                ColumnKind::Payload(_) => {
                    // a literal must be the row's value; a payload variable the
                    // substitution binds must be bound to it
                    let Some(&value) = args.get(i) else {
                        return false;
                    };
                    match self.out.term_dag.get(kids[j]) {
                        Term::Lit(l) => {
                            if !matches!(self.egg().get(value), Term::Lit(m) if m == l) {
                                return false;
                            }
                        }
                        Term::Var(v) => {
                            if let Some(&want) = ctx.subst.get(v)
                                && want != value
                            {
                                return false;
                            }
                        }
                        Term::App(..) => {}
                    }
                    i += 1;
                }
            }
        }
        true
    }
}
