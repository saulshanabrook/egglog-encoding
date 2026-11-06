//! Decode encoded terms and column edges into surface terms.

use super::*;

impl SlotLifter<'_> {
    pub(super) fn slot_map(&self, t: TermId) -> LiftResult<SlotMap> {
        renaming_from_term(self.egg(), t)
            .ok_or_else(|| format!("not a renaming: {}", self.egg_string(t)))
    }

    pub(super) fn group(&self, t: TermId) -> LiftResult<Vec<SlotMap>> {
        group_from_term(self.egg(), t).ok_or_else(|| format!("not a group: {}", self.egg_string(t)))
    }

    /// The group a row's second column holds, naming the row on failure.
    pub(super) fn group_of_row(&self, row: TermId) -> LiftResult<Vec<SlotMap>> {
        let (_, args) = self.app(row).ok_or("not a row")?;
        args.get(1)
            .and_then(|group| group_from_term(self.egg(), *group))
            .ok_or_else(|| format!("row {} holds no group", self.egg_string(row)))
    }

    /// The permutation completing an edge: a slot of the child outside the edge's
    /// domain -- bound, or one the child's class does not depend on -- gets a
    /// fresh name, so that it collides with nothing the parent names.
    pub(super) fn complete(&mut self, m: &SlotMap, child: TermId) -> Renaming {
        let slots = all_slots(&self.out.term_dag, child);
        self.fresh.reserve(m.iter().flat_map(|(k, v)| [*k, *v]));
        let mut entries: Vec<(i64, i64)> = m.iter().map(|(k, v)| (*k, *v)).collect();
        for s in slots {
            if !m.contains_key(&s) {
                let f = self.fresh();
                entries.push((s, f));
            }
        }
        Renaming::completing(entries).expect("an edge's renaming is injective")
    }

    /// The surface term an encoded carrier term denotes.
    pub(super) fn dec(&mut self, t: TermId) -> LiftResult<TermId> {
        if let Some(&d) = self.dec_memo.get(&t) {
            return Ok(d);
        }
        let (head, args) = self
            .app(t)
            .ok_or_else(|| format!("not an encoded carrier term: {}", self.egg_string(t)))?;
        let out = if self.program.constructors.contains_key(head) {
            let head = head.to_string();
            self.build_node(&head, args, None, Some(t))?
        } else {
            return Err(format!(
                "not an encoded carrier term: {}",
                self.egg_string(t)
            ));
        };
        log::debug!("dec {} = {}", self.egg_string(t), self.out_string(out));
        self.dec_memo.insert(t, out);
        Ok(out)
    }

    /// A node's surface term from its constructor's columns: each slotted column
    /// is the child's term under the column's edge completed to a permutation,
    /// and each of the node's own bound slots is named apart. `edges` overrides
    /// the edges the row carries; the completions are recorded under `memo_for`.
    pub(super) fn build_node(
        &mut self,
        head: &str,
        args: &[TermId],
        edges: Option<&[SlotMap]>,
        memo_for: Option<TermId>,
    ) -> LiftResult<TermId> {
        let columns = self
            .program
            .constructors
            .get(head)
            .ok_or_else(|| format!("unknown constructor {head}"))?
            .columns
            .clone();
        let mut children = Vec::with_capacity(columns.len());
        let mut i = 0;
        let mut k = 0;
        // the node's own bound slots, named apart: (column, node slot, new name)
        let mut pending: Vec<(usize, i64, i64)> = vec![];
        for (j, col) in columns.iter().enumerate() {
            match col {
                ColumnKind::Binder => {
                    let m = match edges {
                        Some(e) => e[k].clone(),
                        None => self.slot_map(*args.get(i).ok_or("short row")?)?,
                    };
                    let slot = *m.get(&0).ok_or("a binder column without its slot")?;
                    let b = self.fresh();
                    pending.push((j, slot, b));
                    children.push(slot_term(&mut self.out.term_dag, b));
                    if let Some(t) = memo_for {
                        self.edge_memo
                            .insert((t, j), Renaming::new([(0, b), (b, 0)]).unwrap());
                    }
                    i += 1;
                    k += 1;
                }
                ColumnKind::Var => {
                    let m = match edges {
                        Some(e) => e[k].clone(),
                        None => self.slot_map(*args.get(i).ok_or("short row")?)?,
                    };
                    let slot = *m.get(&0).ok_or("a Var column without its slot")?;
                    children.push(slot_term(&mut self.out.term_dag, slot));
                    i += 1;
                    k += 1;
                }
                ColumnKind::Child => {
                    let m = match edges {
                        Some(e) => e[k].clone(),
                        None => self.slot_map(*args.get(i).ok_or("short row")?)?,
                    };
                    let class = *args.get(i + 1).ok_or("short row")?;
                    let child = self.dec(class)?;
                    let mut completion = self.complete(&m, child);
                    // the binders this column is under, innermost first
                    for (_, slot, b) in pending.drain(..).rev() {
                        let swap = Renaming::new([(slot, b), (b, slot)]).unwrap();
                        completion = swap.compose(&completion);
                    }
                    let renamed = rename(&mut self.out.term_dag, &completion, child);
                    if let Some(t) = memo_for {
                        self.edge_memo.insert((t, j), completion);
                    }
                    children.push(renamed);
                    i += 2;
                    k += 1;
                }
                ColumnKind::Payload(_) => {
                    let lit = match self.egg().get(args[i]) {
                        Term::Lit(l) => l.clone(),
                        _ => return Err(format!("payload is not a literal in {head}")),
                    };
                    children.push(self.out.term_dag.lit(lit));
                    i += 1;
                }
            }
        }
        Ok(self.out.term_dag.app(head.to_string(), children))
    }

    /// Surface column index of an encoded row's physical child index.
    pub(super) fn surface_column(&self, head: &str, physical: usize) -> LiftResult<usize> {
        let ctor = self
            .program
            .constructors
            .get(head)
            .ok_or_else(|| format!("unknown constructor {head}"))?;
        let mut i = 0;
        for (j, col) in ctor.columns.iter().enumerate() {
            let width = match col {
                ColumnKind::Child => 2,
                ColumnKind::Var | ColumnKind::Binder | ColumnKind::Payload(_) => 1,
            };
            if physical == i + width - 1 && width == 2 {
                return Ok(j);
            }
            if physical < i + width {
                return Err(format!(
                    "physical column {physical} of {head} is not a class column"
                ));
            }
            i += width;
        }
        Err(format!(
            "physical column {physical} out of range for {head}"
        ))
    }

    /// The classes in a row's slotted columns, in column order.
    pub(super) fn slotted_classes(&self, row: TermId) -> LiftResult<Vec<Option<TermId>>> {
        let (head, args) = self.app(row).ok_or("not a row")?;
        let ctor = self
            .program
            .constructors
            .get(head)
            .ok_or("unknown constructor")?;
        let mut out = vec![];
        let mut i = 0;
        for col in &ctor.columns {
            match col {
                ColumnKind::Child => {
                    out.push(Some(args[i + 1]));
                    i += 2;
                }
                ColumnKind::Var | ColumnKind::Binder => {
                    out.push(None);
                    i += 1;
                }
                ColumnKind::Payload(_) => i += 1,
            }
        }
        Ok(out)
    }

    /// The equality a row denotes, from a proof of the row: `(a, m, b)` as
    /// surface terms with the completed renaming.
    pub(super) fn row_sides(&mut self, row: TermId) -> LiftResult<(TermId, SlotMap, TermId)> {
        let (head, args) = self.app(row).ok_or("not a row")?;
        match row_kind(head) {
            RowKind::Edge => Ok((args[0], self.slot_map(args[1])?, args[2])),
            RowKind::Invocation => Ok((args[2], self.slot_map(args[1])?, args[0])),
            RowKind::Other => Err(format!("row {} denotes no equality", self.egg_string(row))),
        }
    }

    /// The occurrences of an encoded row: itself, and each slotted column's class.
    pub(super) fn row_occurrences(
        &self,
        row: TermId,
    ) -> LiftResult<HashMap<Vec<usize>, Occurrence>> {
        let mut occ: HashMap<Vec<usize>, Occurrence> = HashMap::default();
        occ.insert(
            vec![],
            Occurrence {
                cls: row,
                row: None,
            },
        );
        let (head, args) = self.app(row).ok_or("not a row")?;
        if let Some(ctor) = self.program.constructors.get(head) {
            let mut i = 0;
            for (j, col) in ctor.columns.iter().enumerate() {
                match col {
                    ColumnKind::Child => {
                        occ.insert(
                            vec![j],
                            Occurrence {
                                cls: args[i + 1],
                                row: None,
                            },
                        );
                        i += 2;
                    }
                    ColumnKind::Var | ColumnKind::Binder => i += 1,
                    ColumnKind::Payload(_) => i += 1,
                }
            }
        }
        Ok(occ)
    }
}
