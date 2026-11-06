//! Reconstruct equalities from canonical node shapes.

use super::*;

#[derive(Clone, PartialEq, Eq, Hash)]
pub(super) struct ShapeKey {
    constructor: String,
    edges: Vec<SlotMap>,
    classes: Vec<Option<TermId>>,
    payloads: Vec<TermId>,
}

impl SlotLifter<'_> {
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
        // the edges and classes of the slotted columns, and the payloads
        let mut edges: Vec<SlotMap> = vec![];
        let mut classes: Vec<Option<TermId>> = vec![];
        let mut payloads: Vec<TermId> = vec![];
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
                ColumnKind::Payload(_) => {
                    payloads.push(args[i]);
                    i += 1;
                }
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
        // the least reading over the children's groups, as node-shape computes it
        let mut best: Option<(Vec<SlotMap>, Vec<SlotMap>)> = None;
        for variant in readings(&edges, &group_values) {
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
            let s = self.symmetry(classes[k].ok_or("rigid port has no class")?, &g, gproof)?;
            let completion = self.edge_memo[&(row, j)].clone();
            let renamed = self.rename_both(s, &completion);
            p = self.out.congr(p, j, renamed).map_err(|e| e.to_string())?;
            p = self.note(p);
        }
        // the shape node: canonical edges over the same children
        let key = ShapeKey {
            constructor: head.clone(),
            edges: canonical_edges.clone(),
            classes: classes.clone(),
            payloads,
        };
        let node = if let Some(&n) = self.shape_terms.get(&key) {
            n
        } else {
            let n = self.build_node(&head, args, Some(&canonical_edges), None)?;
            self.shape_terms.insert(key, n);
            n
        };
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
        let (c0_eq, c0_row, c0_groups) = self.shape_entry(class_row_proof)?;
        if c0_row == row && self.sub(subst, "_c")? == self.sub(subst, "_c0")? {
            // the row met its own entry under another reading: a symmetry of its class
            let c = self.sub(subst, "_c")?;
            let back = self.slot_map(self.sub(subst, "_back")?)?;
            let back0 = self.slot_map(self.sub(subst, "_back0")?)?;
            let g = compose(&back, &inverse(&back0));
            return self.node_symmetry(row_eq, row, &groups, c, &g);
        }
        let (to_shape0, node0) = self.shape_form(c0_eq, c0_row, &c0_groups)?;
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

    /// Through the proof of a `_shape_class_F` row: the stored class's row
    /// equality, the row, and the group rows its index firing read.
    fn shape_entry(&mut self, proof: ProofId) -> LiftResult<(ViewId, TermId, SymmetryPremises)> {
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
                let groups = classes
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
                Ok((row_eq, row, groups))
            }
            Justification::MergeFn { old_proof, .. } => self.shape_entry(*old_proof),
            Justification::Congr {
                proof,
                child_index,
                child_proof,
            } => {
                // the stored class moved: c0 = c0', so the entry's row equality is
                // restated from the new class
                let (row_eq, row, groups) = self.shape_entry(*proof)?;
                let (head, args) = self.app(p.lhs()).ok_or("not a row")?;
                let _ = head;
                if *child_index == args.len() - 1 {
                    let c = self.eq(*child_proof)?;
                    let s = self.out.sym(c);
                    let r = self.trans(s, row_eq)?;
                    Ok((r, row, groups))
                } else {
                    // a child class column of the key moved; the row itself is unchanged
                    Ok((row_eq, row, groups))
                }
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

/// Each column's edge through every element of its child's group that permutes
/// the column's slots, as `node-shape` reads a row; with the elements chosen.
pub(super) fn readings(
    edges: &[SlotMap],
    groups: &[Vec<SlotMap>],
) -> Vec<(Vec<SlotMap>, Vec<SlotMap>)> {
    let columns: Vec<Vec<(SlotMap, SlotMap)>> = edges
        .iter()
        .enumerate()
        .map(|(i, edge)| {
            let domain: BTreeSet<i64> = edge.keys().copied().collect();
            let identity: SlotMap = domain.iter().map(|s| (*s, *s)).collect();
            let mut out: Vec<(SlotMap, SlotMap)> = vec![(edge.clone(), identity)];
            for g in groups.get(i).map(Vec::as_slice).unwrap_or_default() {
                if g.keys().copied().collect::<BTreeSet<_>>() == domain
                    && g.values().copied().collect::<BTreeSet<_>>() == domain
                {
                    let read: SlotMap = g.iter().map(|(&s, &t)| (s, edge[&t])).collect();
                    if !out.iter().any(|(r, _)| *r == read) {
                        out.push((read, g.clone()));
                    }
                }
            }
            out
        })
        .collect();
    let total: usize = columns.iter().map(Vec::len).product();
    (0..total)
        .map(|mut n| {
            let mut variant = Vec::with_capacity(columns.len());
            let mut chosen = Vec::with_capacity(columns.len());
            for column in &columns {
                let (read, g) = &column[n % column.len()];
                variant.push(read.clone());
                chosen.push(g.clone());
                n /= column.len();
            }
            (variant, chosen)
        })
        .collect()
}
