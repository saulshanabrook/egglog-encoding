//! Reconstruct equalities from canonical node shapes.

use super::*;

#[derive(Clone, PartialEq, Eq, Hash)]
pub(super) struct ShapeKey {
    constructor: String,
    edges: Vec<SlotMap>,
    classes: Vec<Option<TermId>>,
    payloads: Vec<TermId>,
}

struct ShapeEntry {
    proof: ViewId,
    node: TermId,
    row: TermId,
}

impl SlotLifter<'_> {
    fn shape_key(&self, head: &str, args: &[TermId]) -> LiftResult<ShapeKey> {
        let mut key = ShapeKey {
            constructor: head.to_owned(),
            edges: Vec::new(),
            classes: Vec::new(),
            payloads: Vec::new(),
        };
        let mut i = 0;
        for column in &self.program.constructors[head].columns {
            match column {
                ColumnKind::Child => {
                    key.edges.push(self.slot_map(args[i])?);
                    key.classes.push(Some(args[i + 1]));
                    i += 2;
                }
                ColumnKind::Var | ColumnKind::Binder => {
                    key.edges.push(self.slot_map(args[i])?);
                    key.classes.push(None);
                    i += 1;
                }
                ColumnKind::Payload(_) => {
                    key.payloads.push(args[i]);
                    i += 1;
                }
            }
        }
        Ok(key)
    }

    fn shape_node(&mut self, key: ShapeKey, args: &[TermId]) -> LiftResult<TermId> {
        if let Some(&node) = self.shape_terms.get(&key) {
            return Ok(node);
        }
        let node = self.build_node(&key.constructor, args, Some(&key.edges), None)?;
        self.shape_terms.insert(key, node);
        Ok(node)
    }

    /// `dec(row) = back·N` where `N` is the row's node spelled with its canonical
    /// edges: the readings `g_i` of the children that make the edges canonical,
    /// applied by congruence, then the renaming back.
    fn shape_form(
        &mut self,
        row_eq: ViewId,
        row: TermId,
        groups: &[Option<(TermId, ProofId)>],
    ) -> LiftResult<(ViewId, TermId)> {
        let (head, args) = self.app(row).ok_or("not a row")?;
        let head = head.to_string();
        let ctor = self
            .program
            .constructors
            .get(&head)
            .ok_or("unknown constructor")?
            .clone();
        let mut key = self.shape_key(&head, args)?;
        let group_values: Vec<Vec<SlotMap>> = groups
            .iter()
            .map(|group| match group {
                Some((g, _)) => self.group(*g),
                None => Ok(vec![[(0, 0)].into_iter().collect()]),
            })
            .collect::<LiftResult<_>>()?;
        let own = shape(&key.edges);
        // the least reading over the children's groups, as node-shape computes it
        let mut best: Option<(Vec<SlotMap>, Vec<SlotMap>)> = None;
        for variant in readings(&key.edges, &group_values) {
            let spelled = shape(&variant.0);
            if best.as_ref().is_none_or(|b| spelled.edges < b.0) {
                best = Some((spelled.edges, variant.1));
            }
        }
        let (canonical_edges, gs) = best.unwrap_or((own.edges.clone(), vec![]));
        let _ = own;
        // apply each child's reading by congruence: child j: m̂_j·dec(c_j) = (m̂_j∘ĝ_j)·dec(c_j)
        let mut p = row_eq;
        let mut slotted_j = 0;
        for (j, col) in ctor.columns.iter().enumerate() {
            if matches!(col, ColumnKind::Payload(_)) {
                continue;
            }
            let k = slotted_j;
            slotted_j += 1;
            let g = match gs.get(k) {
                Some(g) if !is_identity(g) => g.clone(),
                _ => continue,
            };
            let (gterm, gproof) = groups[k].ok_or("a rigid port has a nonidentity reading")?;
            let _ = gterm;
            let s = self.symmetry(key.classes[k].ok_or("rigid port has no class")?, &g, gproof)?;
            let completion = self.edge_memo[&(row, j)].clone();
            let renamed = self.rename_both(s, &completion);
            p = self.out.congr(p, j, renamed).map_err(|e| e.to_string())?;
            p = self.note(p);
        }
        key.edges = canonical_edges;
        let node = self.shape_node(key, args)?;
        // `p` now ends in the row spelled through the readings; align its coordinates with the shape node
        let aligned = self.align(p, node)?;
        Ok((aligned, node))
    }

    /// Two rows meeting on one shape: `c = (back∘back0⁻¹)·c0`.
    pub(super) fn shape_collision(
        &mut self,
        prems: &[ProofId],
        subst: &IndexMap<String, TermId>,
    ) -> LiftResult<ViewId> {
        // premises: c = row, g1.., shapeof-edges row, (vec-get facts), c0 = shape-class row, back0 row, guard
        let row_eq = self.eq(prems[0])?;
        let row = self.egg.get(prems[0]).rhs();
        let classes = self.slotted_classes(row)?;
        let groups: SymmetryPremises = classes
            .iter()
            .enumerate()
            .map(|(k, &class)| {
                class
                    .map(|class| {
                        let g = self.sub(subst, &format!("_g{}", k + 1))?;
                        Ok((g, self.group_premise(prems, class)?))
                    })
                    .transpose()
            })
            .collect::<LiftResult<_>>()?;
        let (to_shape, node) = self.shape_form(row_eq, row, &groups)?;
        // the stored class: through the proof of the `_shape_class` row
        let class_row_proof = prems
            .iter()
            .copied()
            .find(|p| {
                let t = self.egg.get(*p).lhs();
                self.app(t)
                    .is_some_and(|(h, _)| h.starts_with("_shape_class_"))
            })
            .ok_or("shape-collision without its class row")?;
        let entry = self.shape_entry(class_row_proof)?;
        if entry.row == row && self.sub(subst, "_c")? == self.sub(subst, "_c0")? {
            // the row met its own entry under another reading: a symmetry of its class
            let c = self.sub(subst, "_c")?;
            let back = self.slot_map(self.sub(subst, "_back")?)?;
            let back0 = self.slot_map(self.sub(subst, "_back0")?)?;
            let g = compose(&back, &inverse(&back0));
            return self.node_symmetry(row_eq, row, &groups, c, &g);
        }
        let (to_shape0, node0) = (entry.proof, entry.node);
        if node0 != node {
            return Err(format!(
                "shape collision on different nodes {} and {}",
                self.out_string(node),
                self.out_string(node0)
            ));
        }
        let s = self.out.sym(to_shape0);
        self.trans(to_shape, s)
    }

    /// Two rows of one class with one shape: the symmetry between them.
    pub(super) fn shape_dedup(
        &mut self,
        prems: &[ProofId],
        subst: &IndexMap<String, TermId>,
    ) -> LiftResult<ViewId> {
        let row1_eq = self.eq(prems[0])?;
        let row1 = self.egg.get(prems[0]).rhs();
        let classes = self.slotted_classes(row1)?;
        let groups: SymmetryPremises = classes
            .iter()
            .enumerate()
            .map(|(k, &class)| {
                class
                    .map(|class| {
                        Ok((
                            self.sub(subst, &format!("_g{}", k + 1))?,
                            self.group_premise(prems, class)?,
                        ))
                    })
                    .transpose()
            })
            .collect::<LiftResult<_>>()?;
        // Normalizing literal rigid groups can insert primitive premises before
        // the second row, so its index is not fixed. Only the two constructor
        // rows have this class as their left endpoint.
        let head = self.app(row1).ok_or("not a constructor row")?.0;
        let class = self.egg.get(prems[0]).lhs();
        let row2_prem = prems
            .iter()
            .copied()
            .skip(1)
            .find(|&id| {
                let proof = self.egg.get(id);
                proof.lhs() == class
                    && proof.rhs() != row1
                    && self
                        .app(proof.rhs())
                        .is_some_and(|(other, _)| other == head)
            })
            .ok_or("shape dedup has no second constructor row")?;
        let row2_eq = self.eq(row2_prem)?;
        let row2 = self.egg.get(row2_prem).rhs();
        let (a, node) = self.shape_form(row1_eq, row1, &groups)?;
        let (b, node2) = self.shape_form(row2_eq, row2, &groups)?;
        if node != node2 {
            return Err("dedup rows have different shapes".into());
        }
        let s = self.out.sym(b);
        self.trans(a, s)
    }

    /// The stored class equals its indexed canonical node. Rebuilding can change
    /// either the stored class or a child in the key; both changes carry proofs.
    fn shape_entry(&mut self, proof: ProofId) -> LiftResult<ShapeEntry> {
        let p = self.egg.get(proof).clone();
        match p.justification() {
            Justification::Rule {
                name,
                premise_proofs,
                substitution,
            } if rule_kind(self.program, name) == RuleKind::ShapeIndex => {
                let row_eq = self.eq(premise_proofs[0])?;
                let row = self.egg.get(premise_proofs[0]).rhs();
                let classes = self.slotted_classes(row)?;
                let groups: SymmetryPremises = classes
                    .iter()
                    .enumerate()
                    .map(|(k, &class)| {
                        class
                            .map(|class| {
                                Ok((
                                    self.sub(substitution, &format!("_g{}", k + 1))?,
                                    self.group_premise(premise_proofs, class)?,
                                ))
                            })
                            .transpose()
                    })
                    .collect::<LiftResult<_>>()?;
                let (proof, node) = self.shape_form(row_eq, row, &groups)?;
                Ok(ShapeEntry { proof, node, row })
            }
            Justification::MergeFn { old_proof, .. } => self.shape_entry(*old_proof),
            Justification::Congr {
                proof,
                child_index,
                child_proof,
            } => {
                let mut entry = self.shape_entry(*proof)?;
                let (head, args) = self.app(p.lhs()).ok_or("not a shape entry")?;
                if *child_index == args.len() - 1 {
                    let child = self.eq(*child_proof)?;
                    let reverse = self.out.sym(child);
                    entry.proof = self.trans(reverse, entry.proof)?;
                } else if self.egg.get(*child_proof).lhs() != self.egg.get(*child_proof).rhs() {
                    let head = head
                        .strip_prefix("_shape_class_")
                        .ok_or("not a shape class")?;
                    let column = self.surface_column(head, *child_index)?;
                    let old = self.dec(args[*child_index])?;
                    let at = self.subterm_at(entry.node, &[column])?;
                    let mapping = term_renaming(&self.out.term_dag, &[(old, at)])
                        .ok_or("shape key child does not match its recorded node")?;
                    let child = self.eq(*child_proof)?;
                    let child = self.rename_both(child, &mapping);
                    let updated = self
                        .out
                        .congr(entry.proof, column, child)
                        .map_err(|e| e.to_string())?;
                    let (_, args) = self.app(p.rhs()).ok_or("not a rebuilt shape entry")?;
                    let key = self.shape_key(head, args)?;
                    entry.node = self.shape_node(key, args)?;
                    entry.proof = self.fit(updated, entry.node, &HashMap::default())?;
                }
                Ok(entry)
            }
            Justification::Trans(a, b) => {
                let _ = b;
                self.shape_entry(*a)
            }
            Justification::Sym(a) => self.shape_entry(*a),
            other => Err(format!("unexpected shape entry provenance {other:?}")),
        }
    }
}
