//! Prove that redundant names may be permuted.

use super::*;

impl SlotLifter<'_> {
    /// Every proof in the egglog store of a `FreeVars` row, by its class term.
    fn free_vars_proofs(&mut self, cls: TermId) -> Vec<ProofId> {
        self.free_vars_index
            .get_or_insert_with(|| row_proofs(self.egg, "FreeVars_"))
            .get(&cls)
            .cloned()
            .unwrap_or_default()
    }

    /// `dec(c) = (s f)·dec(c)`: slot `s` of `c`'s term is one its class does not
    /// depend on, so it may be renamed to the unused `f`. Derived from how the
    /// class's slot set came to exclude `s`.
    fn class_cert(&mut self, c: TermId, s: i64, f: i64) -> LiftResult<ViewId> {
        let t = self.dec(c)?;
        log::debug!("class_cert {} slot {s} -> {f}", self.out_string(t));
        let slots = all_slots(&self.out.term_dag, t);
        if !slots.contains(&s) {
            if slots.contains(&f) {
                return Err("redundancy certificate target is not fresh".into());
            }
            let proof = self.reflexive(t)?;
            // Transport still needs this swap when neither name occurs in t.
            let swap = Renaming::new([(s, f), (f, s)]).unwrap();
            let proof = self.out.reframe(proof, swap);
            return Ok(self.note(proof));
        }
        if !self.cert_stack.insert((c, s)) {
            return Err(format!(
                "the certificate for ${s} in {} depends on itself",
                self.out_string(t)
            ));
        }
        let r = self.class_cert_inner(c, s, f);
        self.cert_stack.remove(&(c, s));
        r
    }

    fn class_cert_inner(&mut self, c: TermId, s: i64, f: i64) -> LiftResult<ViewId> {
        let t = self.dec(c)?;
        let proofs = self.free_vars_proofs(c);
        let mut errors = vec![];
        for proof in proofs {
            let (_, args) = self.app(self.egg.get(proof).lhs()).ok_or("not a row")?;
            let cs = self.slot_map(args[1])?;
            if cs.contains_key(&s) {
                continue;
            }
            match self.cert_from(proof, c, s, f) {
                Ok(p) => return Ok(p),
                Err(e) => errors.push(e),
            }
        }
        Err(format!(
            "no certificate that ${s} is redundant in {}: {}",
            self.out_string(t),
            if errors.is_empty() {
                "no FreeVars row excludes it".to_string()
            } else {
                errors.join("; ")
            }
        ))
    }

    /// The certificate for `(c, s, f)` through one proof of a `FreeVars` row
    /// that excludes `s`.
    fn cert_from(&mut self, proof: ProofId, c: TermId, s: i64, f: i64) -> LiftResult<ViewId> {
        let p = self.egg.get(proof).clone();
        match p.justification().clone() {
            Justification::Rule {
                name,
                premise_proofs: prems,
                substitution: subst,
            } => match rule_kind(self.program, &name) {
                RuleKind::ClassSlots => {
                    // the class is the row, `c = M·row`: a slot the row's content does
                    // not mention is redundant outright; otherwise s is not a node slot
                    // of the row, so it belongs to a child's term, where the child's
                    // class does not depend on it
                    let row = self.egg.get(prems[0]).rhs();
                    let row_eq = self.eq(prems[0])?; // c = M·row
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
                                let cert = self.class_cert(child, r, fi)?;
                                let lifted = self.rename_both(cert, &completion); // occ = ·child
                                let lifted = self.out.reframe(lifted, completion.clone()); // occ = (s f)·occ
                                let lifted = self.note(lifted);
                                let refl = self.reflexive(prop.rhs)?;
                                let r =
                                    self.out.congr(refl, j, lifted).map_err(|e| e.to_string())?; // row = ·row[s->f]
                                let r = self.note(r);
                                let r = self.out.reframe(
                                    r,
                                    Renaming::new([(s_row, f_row), (f_row, s_row)]).unwrap(),
                                );
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
                    let cert_a = self.class_cert(a, x, fa)?;
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
                    let cert_b = self.class_cert(b, r, fb)?;
                    self.transport(cert_b, edge)
                }
                RuleKind::SlotClosure => {
                    let grp = self.group(self.sub(&subst, "_grp")?)?;
                    let old = self.slot_map(self.sub(&subst, "_slots")?)?;
                    let t = self.dec(c)?;
                    // the symmetries behind the group, as stated: a group element
                    // restricted to the class's slots may have lost the entry
                    // that drops the slot
                    let mut syms: Vec<ViewId> = vec![];
                    for g in grp.iter().filter(|g| !is_identity(g)) {
                        if let Ok(sp) = self.symmetry(c, g, prems[0]) {
                            syms.push(sp);
                        }
                    }
                    let grp_row = prems
                        .iter()
                        .copied()
                        .find(|q| {
                            let t = self.egg.get(*q).lhs();
                            self.app(t)
                                .is_some_and(|(h, _)| h.starts_with("EclassGroup_"))
                        })
                        .unwrap_or(prems[0]);
                    let mut errors = vec![];
                    match self.symmetry_sources(grp_row) {
                        Ok(more) => syms.extend(more),
                        Err(e) => errors.push(e),
                    }
                    for sym in syms {
                        let prop = self.out.edge(sym).clone(); // t = ĝ·t
                        if prop.lhs != t || prop.rhs != t {
                            continue;
                        }
                        let content = rename(&mut self.out.term_dag, &prop.renaming, t);
                        if !all_slots(&self.out.term_dag, content).contains(&s) {
                            return self.lemma(sym, s, f);
                        }
                        // the conjugation needs a name the symmetry leaves alone:
                        // a fresh one, renamed to f at the end
                        let g = self.fresh();
                        // s = ĝ(y): a slot y the old set lacks gives s through the symmetry
                        let y = prop.renaming.inverse().apply(s);
                        if y != s
                            && !old.contains_key(&y)
                            && all_slots(&self.out.term_dag, t).contains(&y)
                            && let Ok(cert_y) = self.class_cert(c, y, g)
                        {
                            // t = ĝ·t ; t = (y g)·t ; t = ĝ⁻¹·t  →  (ĝ∘(y g)∘ĝ⁻¹) = (s g)
                            let s1 = self.out.sym(sym); // t = ĝ⁻¹·t
                            let left = self.trans(sym, cert_y)?; // t = (ĝ∘(y g))·t
                            let r = self.trans(left, s1)?;
                            return Ok(self.retarget(r, g, f));
                        }
                        let z = prop.renaming.apply(s);
                        if z != s
                            && !old.contains_key(&z)
                            && all_slots(&self.out.term_dag, t).contains(&z)
                            && let Ok(cert_z) = self.class_cert(c, z, g)
                        {
                            let s1 = self.out.sym(sym); // t = ĝ⁻¹·t
                            let left = self.trans(s1, cert_z)?; // t = (ĝ⁻¹∘(z g))·t
                            let r = self.trans(left, sym)?;
                            return Ok(self.retarget(r, g, f));
                        }
                    }
                    Err(format!(
                        "no symmetry drops ${s}{}",
                        if errors.is_empty() {
                            String::new()
                        } else {
                            format!(" ({})", errors.join("; "))
                        }
                    ))
                }
                other => Err(format!("no certificate through rule {other:?}")),
            },
            Justification::MergeFn {
                old_proof,
                new_proof,
                ..
            } => {
                for side in [old_proof, new_proof] {
                    let t = self.egg.get(side).lhs();
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
                let c0 = self.app(self.egg.get(base).lhs()).ok_or("not a row")?.1[0];
                let e = self.eq(child_proof)?; // c0 = n·c
                let n = self.out.edge(e).renaming.clone();
                let cert0 = self.class_cert(c0, n.apply(s), n.apply(f))?;
                let q = self.out.sym(e); // c = n⁻¹·c0
                let q = self.note(q);
                self.transport(cert0, q)
            }
            Justification::Trans(a, b) => self
                .cert_from(a, c, s, f)
                .or_else(|_| self.cert_from(b, c, s, f)),
            Justification::Sym(a) => self.cert_from(a, c, s, f),
            Justification::Fiat => Err("a slot set stated by fiat".into()),
            other => Err(format!("no certificate through {other:?}")),
        }
    }

    /// From `P: L = m·R` whose content (`m·R`) does not mention `s`, with `s` a
    /// slot of `L` and `f` unused: `L = (s f)·L`.
    fn lemma(&mut self, p: ViewId, s: i64, f: i64) -> LiftResult<ViewId> {
        let pc = self.content_form(p); // L = C
        let content = self.out.edge(pc).rhs;
        let slots = all_slots(&self.out.term_dag, content);
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
    fn transport(&mut self, cert: ViewId, q: ViewId) -> LiftResult<ViewId> {
        let left = self.trans(q, cert)?; // Y = (N∘τ)·X
        let back = self.out.sym(q); // X = N⁻¹·Y
        self.trans(left, back)
    }

    /// `O = (x y)·O` for the occurrence term `O` of class `c` (a renaming of its
    /// term), where `x` is a slot of `O` the class does not depend on and `y` is
    /// not in `O`.
    pub(super) fn occurrence_cert(
        &mut self,
        o: Occurrence,
        occ: TermId,
        x: i64,
        y: i64,
    ) -> LiftResult<ViewId> {
        // the occurrence is a renaming of the class's term, or of the row the
        // atom there matched
        let d = self.dec(o.cls)?;
        let mut pairs = BTreeMap::new();
        let (base, rho) = if self.match_slots(d, occ, &mut pairs).is_ok()
            && let Some(rho) = Renaming::completing(pairs.iter().map(|(k, v)| (*k, *v)))
        {
            (None, rho)
        } else if let Some((row, row_eq)) = o.row {
            let dr = self.dec(row)?;
            let mut pairs = BTreeMap::new();
            self.unify_slots(dr, occ, &mut pairs).map_err(|e| {
                format!(
                    "occurrence {} is neither a renaming of {} nor of {}: {e}",
                    self.out_string(occ),
                    self.out_string(d),
                    self.out_string(dr)
                )
            })?;
            let rho = Renaming::completing(pairs.into_iter())
                .ok_or("non-injective occurrence renaming")?;
            (Some((row, row_eq)), rho)
        } else {
            return Err(format!(
                "occurrence {} is not a renaming of {}",
                self.out_string(occ),
                self.out_string(d)
            ));
        };
        let s = rho.inverse().apply(x);
        let f = rho.inverse().apply(y);
        let cert = match base {
            None => self.class_cert(o.cls, s, f)?, // d = (s f)·d
            Some((_, row_eq)) => {
                // the row's slot through the class: cls = N·row
                let q = self.out.sym(row_eq); // row = N⁻¹·cls
                let q = self.note(q);
                let qp = self.out.edge(q).clone();
                let through = rename(&mut self.out.term_dag, &qp.renaming, qp.rhs);
                if !all_slots(&self.out.term_dag, through).contains(&s) {
                    // the class's term does not mention it at all
                    self.lemma(q, s, f)?
                } else {
                    let n = self.out.edge(row_eq).renaming.clone();
                    let cert_cls = self.class_cert(o.cls, n.apply(s), n.apply(f))?;
                    self.transport(cert_cls, q)? // row = (s f)·row
                }
            }
        };
        let lifted = self.rename_both(cert, &rho); // ρX = (ρ∘(s f))·X
        let lifted = self.out.reframe(lifted, rho); // ρX = (ρ∘(s f)∘ρ⁻¹)·ρX
        Ok(self.note(lifted))
    }

    /// `O = (x y ..)·O` for the occurrence term `O` of class `c`: a symmetry of
    /// the class that sends `x` to `y`, spelled on the occurrence.
    pub(super) fn occurrence_symmetry(
        &mut self,
        o: Occurrence,
        occ: TermId,
        x: i64,
        y: i64,
    ) -> LiftResult<ViewId> {
        let d = self.dec(o.cls)?;
        let mut pairs = BTreeMap::new();
        let (base, rho) = if self.match_slots(d, occ, &mut pairs).is_ok()
            && let Some(rho) = Renaming::completing(pairs.iter().map(|(k, v)| (*k, *v)))
        {
            (None, rho)
        } else if let Some((row, row_eq)) = o.row {
            let dr = self.dec(row)?;
            let mut pairs = BTreeMap::new();
            self.unify_slots(dr, occ, &mut pairs)?;
            let rho = Renaming::completing(pairs.into_iter())
                .ok_or("non-injective occurrence renaming")?;
            (Some((row, row_eq)), rho)
        } else {
            return Err(format!(
                "occurrence {} is not a renaming of {}",
                self.out_string(occ),
                self.out_string(d)
            ));
        };
        let (s, f) = (rho.inverse().apply(x), rho.inverse().apply(y));
        // in the class's own coordinates
        let n = match base {
            None => Renaming::identity(),
            Some((_, row_eq)) => self.out.edge(row_eq).renaming.clone(),
        };
        let (cs, cf) = (n.apply(s), n.apply(f));
        let mut errors = vec![];
        let mut sym: Option<ViewId> = None;
        for proof in self.group_proofs(o.cls) {
            let elements = match self.group_of_row(self.egg.get(proof).lhs()) {
                Ok(e) => e,
                Err(e) => {
                    errors.push(e);
                    continue;
                }
            };
            for g in elements.iter().filter(|g| g.get(&cs) == Some(&cf)) {
                match self.symmetry(o.cls, g, proof) {
                    Ok(p) => {
                        sym = Some(p);
                        break;
                    }
                    Err(e) => errors.push(e),
                }
            }
            if sym.is_some() {
                break;
            }
        }
        let Some(cert) = sym else {
            return Err(format!(
                "no symmetry of {} sends ${cs} to ${cf}{}",
                self.out_string(d),
                if errors.is_empty() {
                    String::new()
                } else {
                    format!(" ({})", errors.join("; "))
                }
            ));
        };
        let cert = match base {
            None => cert,
            Some((_, row_eq)) => {
                let q = self.out.sym(row_eq); // row = N⁻¹·cls
                let q = self.note(q);
                self.transport(cert, q)?
            }
        };
        let lifted = self.rename_both(cert, &rho);
        let lifted = self.out.reframe(lifted, rho);
        Ok(self.note(lifted))
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
