//! Replay source globals and rule heads at their recorded native positions.

use super::*;
use egglog::ast::{GenericAction, ResolvedExpr, ResolvedExprExt, ResolvedNCommand, ResolvedVar};
type ResolvedAction = GenericAction<egglog::ResolvedCall, ResolvedVar>;
use egglog::proof::ProofOrigin;

#[derive(Clone, Debug, Default)]
pub(in crate::slotted::proofs) struct Certificates {
    pub store: SlottedProofStore,
    pub roots: Vec<ProofId>,
    pub anchors: super::HashMap<ProofId, ProofId>,
    /// Ordinary source equalities for restricted head children. Native keys
    /// belong only to the current lifting batch, like the source anchors.
    pub head_supports: super::HashMap<(ProofId, usize), ProofId>,
}

pub(in crate::slotted::proofs) struct SourceLifter<'a> {
    program: &'a ProofContext,
    globals: GlobalCursor<'a>,
    names: &'a EncodingNames,
    pub store: SlottedProofStore,
    pub proofs: HashMap<ProofId, ProofId>,
    certificates: &'a [ProofId],
    error: Option<String>,
    lifting: Option<SlotLifter<'a, ()>>,
}

impl<'a> SourceLifter<'a> {
    pub(in crate::slotted::proofs) fn new(
        program: &'a ProofContext,
        source: &'a super::super::ResolvedSlottedProgram,
        names: &'a EncodingNames,
        evidence: &'a Certificates,
    ) -> Self {
        Self {
            program,
            globals: GlobalCursor::new(program, source, &evidence.roots),
            names,
            store: evidence.store.clone(),
            proofs: HashMap::default(),
            certificates: &evidence.roots,
            error: None,
            lifting: None,
        }
    }

    pub(in crate::slotted::proofs) fn visit(
        &mut self,
        egg: &ProofStore,
        id: ProofId,
        origin: ProofOrigin<'_>,
    ) {
        if self.error.is_some() {
            return;
        }
        match self.replay(egg, id, origin) {
            Ok(Some(proof)) => {
                self.proofs.insert(id, proof);
            }
            Ok(None) => {}
            Err(error) => self.error = Some(error),
        }
    }

    pub(in crate::slotted::proofs) fn finish(mut self) -> LiftResult<Certificates> {
        let mut head_supports = HashMap::default();
        if let Some(mut lifting) = self.lifting {
            self.store = std::mem::take(&mut *lifting.out);
            head_supports = lifting.head_supports;
        }
        match self.error {
            Some(error) => Err(error),
            None => Ok(Certificates {
                store: self.store,
                roots: self.certificates.to_vec(),
                anchors: self.proofs,
                head_supports,
            }),
        }
    }

    fn replay(
        &mut self,
        egg: &ProofStore,
        id: ProofId,
        origin: ProofOrigin<'_>,
    ) -> LiftResult<Option<ProofId>> {
        let (native, selected) = match &origin {
            ProofOrigin::GlobalTerm {
                program, action, ..
            }
            | ProofOrigin::GlobalUnion {
                program, action, ..
            } => (*program, *action),
            ProofOrigin::Rule {
                program,
                rule,
                action,
                path,
            } => {
                return self.rule(
                    NativeProofs {
                        store: egg,
                        program,
                    },
                    id,
                    rule,
                    *action,
                    path,
                );
            }
        };
        let Term::App(head, _) = egg.term_dag().get(egg.get(id).lhs()) else {
            return Ok(None);
        };
        if !self.program.constructors.contains_key(head) && !head.starts_with("Equated_") {
            return Ok(None);
        }
        let global = self
            .globals
            .at(native, selected, self.program, &self.store)?;
        let ResolvedNCommand::CoreAction(action) = &native[global.command] else {
            unreachable!("the global cursor selects actions")
        };
        let (source_lhs, source_rhs, certificate) = (global.lhs, global.rhs, global.certificate);
        let result = match action {
            ResolvedAction::Let(_, _, expression)
                if self.program.sorts.contains(expression.output_type().name()) =>
            {
                let ProofOrigin::GlobalTerm { path, .. } = origin else {
                    return Err("a global binding cannot justify a union".into());
                };
                let proof = self.store.fiat(source_rhs, source_rhs);
                self.descend(expression, &path[1..], proof)?
            }
            ResolvedAction::Union(_, lhs, rhs) => match origin {
                ProofOrigin::GlobalUnion { swapped, .. } => {
                    let (lhs, rhs) = if swapped {
                        (source_rhs, source_lhs)
                    } else {
                        (source_lhs, source_rhs)
                    };
                    self.store.fiat(lhs, rhs)
                }
                ProofOrigin::GlobalTerm { path, .. } => {
                    let side = path[0];
                    let (expression, term) = if side == 0 {
                        (lhs, source_lhs)
                    } else {
                        (rhs, source_rhs)
                    };
                    let proof = self.store.fiat(term, term);
                    self.descend(expression, &path[1..], proof)?
                }
                _ => unreachable!(),
            },
            ResolvedAction::Expr(_, ResolvedExpr::Call(_, call, args))
                if call.name().starts_with("Equated_") =>
            {
                let proof = certificate.ok_or("substitution output lacks its input certificate")?;
                let ProofOrigin::GlobalTerm { path, .. } = origin else {
                    return Err("a substitution insertion cannot justify a native union".into());
                };
                match path.get(1) {
                    None => proof,
                    Some(&side @ (0 | 2)) => {
                        let proof = if side == 0 {
                            self.store.sym(proof)
                        } else {
                            proof
                        };
                        self.descend(&args[side], &path[2..], proof)?
                    }
                    _ => return Err("a substitution carrier proof points into its renaming".into()),
                }
            }
            other => {
                return Err(format!(
                    "global action {selected} has no slotted source occurrence: {other}"
                ));
            }
        };
        Ok(Some(result))
    }

    fn rule(
        &mut self,
        egg: NativeProofs<'_>,
        id: ProofId,
        rule: &egglog::ast::ResolvedRule,
        action: usize,
        path: &[usize],
    ) -> LiftResult<Option<ProofId>> {
        let RuleKind::Apply(name) = rule_kind(self.program, &rule.name) else {
            return Ok(None);
        };
        let proof = egg.get(id);
        let Term::App(head, _) = egg.term_dag().get(proof.lhs()) else {
            return Ok(None);
        };
        if !self.program.constructors.contains_key(head) || proof.lhs() != proof.rhs() {
            return Ok(None);
        }
        let built_path = self.built_path(name, rule, action, path)?;
        let mut lifting = match self.lifting.take() {
            Some(lifting) => lifting.with_egg(egg),
            None => {
                let evidence = Certificates {
                    store: std::mem::take(&mut self.store),
                    roots: self.certificates.to_vec(),
                    anchors: self.proofs.clone(),
                    head_supports: HashMap::default(),
                };
                SlotLifter::with_evidence(
                    self.program,
                    evidence.store.term_dag.clone(),
                    self.names,
                    egg,
                    &evidence,
                )?
            }
        };
        let Justification::Rule {
            premise_proofs,
            substitution,
            ..
        } = proof.justification()
        else {
            return Err("a recorded head conclusion is not a rule proof".into());
        };
        let result = lifting.derive_rule(
            name,
            premise_proofs,
            substitution,
            &HashMap::default(),
            Some((proof.lhs(), proof.rhs())),
            Some((id, &built_path)),
        );
        let result = result
            .map_err(|error| format!("replaying head {id} of {name} at {built_path:?}: {error}"))
            .map(|view| {
                lifting.eq_memo.insert(id, view);
                lifting.out.proof(view)
            });
        self.lifting = Some(lifting.with_egg(()));
        result.map(Some)
    }

    fn built_path(
        &self,
        name: &str,
        rule: &egglog::ast::ResolvedRule,
        action: usize,
        path: &[usize],
    ) -> LiftResult<Vec<usize>> {
        use crate::slotted::model::Term as SourceTerm;
        fn term(expr: &ResolvedExpr) -> SourceTerm {
            match expr {
                ResolvedExpr::Var(_, variable) => match variable.sort.name() {
                    "Var" => SourceTerm::Slot(variable.name.clone()),
                    _ if variable.sort.is_eq_sort() => SourceTerm::Variable(variable.name.clone()),
                    _ => SourceTerm::PayloadVariable(variable.name.clone()),
                },
                ResolvedExpr::Lit(_, literal) => SourceTerm::Payload(literal.to_string()),
                ResolvedExpr::Call(_, call, args) => {
                    SourceTerm::Node(call.name().to_owned(), args.iter().map(term).collect())
                }
            }
        }
        let carrier_binding = |action: &ResolvedAction| matches!(action, ResolvedAction::Let(_, _, value) if self.program.sorts.contains(value.output_type().name()));
        let (mut source_path, expression) = match &rule.head.0[action] {
            ResolvedAction::Let(_, _, expression) if carrier_binding(&rule.head.0[action]) => {
                if path.first() != Some(&0) {
                    return Err("a constructed binding has an invalid operand path".into());
                }
                let selected = rule.head.0[..action]
                    .iter()
                    .filter(|a| carrier_binding(a))
                    .count();
                let (_, rhs) = self.program.rewrites[name].endpoints();
                let source = term(rhs);
                let mut next = 0;
                let mut found = None;
                crate::slotted::rewrite::fold_rhs(
                    &|head| &self.program.constructors[head],
                    &source,
                    rhs.output_type().name(),
                    &mut Vec::new(),
                    &mut |_, _, path, _, bind| {
                        if bind {
                            if next == selected {
                                found = Some(path.to_vec());
                            }
                            next += 1;
                        }
                        Ok(())
                    },
                )?;
                (
                    found.ok_or("constructed head binding has no source occurrence")?,
                    expression,
                )
            }
            ResolvedAction::Union(_, lhs, _) if path.first() == Some(&0) => (vec![], lhs),
            _ => return Err("constructed head term has no source operand".into()),
        };
        let mut expression = expression;
        for &physical in &path[1..] {
            let ResolvedExpr::Call(_, call, args) = expression else {
                return Err("constructed head path continues below a variable".into());
            };
            let constructor = self
                .program
                .constructors
                .get(call.name())
                .ok_or("constructed head path passes through a non-constructor")?;
            let (source, _, _) = constructor
                .encoded_columns()
                .find(|(_, column, range)| {
                    **column == ColumnKind::Child && range.end - 1 == physical
                })
                .ok_or("constructed head path is not a carrier child")?;
            source_path.push(source);
            expression = &args[physical];
        }
        Ok(source_path)
    }

    fn descend(
        &mut self,
        expression: &ResolvedExpr,
        path: &[usize],
        mut proof: ProofId,
    ) -> LiftResult<ProofId> {
        let Some((&physical, rest)) = path.split_first() else {
            return Ok(proof);
        };
        let ResolvedExpr::Call(_, call, args) = expression else {
            return Err("source occurrence continues below a global reference".into());
        };
        let constructor =
            self.program.constructors.get(call.name()).ok_or_else(|| {
                format!("source occurrence is below non-constructor {}", call.name())
            })?;
        let Term::App(head, _) = self.store.term_dag.get(self.store.proposition(proof).rhs) else {
            return Err("source occurrence is not a constructor term".into());
        };
        if head != call.name() {
            return Err(format!(
                "recorded occurrence of {} has source constructor {head}",
                call.name()
            ));
        }
        let (source, _, _) = constructor
            .encoded_columns()
            .find(|(_, column, range)| **column == ColumnKind::Child && range.end - 1 == physical)
            .ok_or_else(|| {
                format!(
                    "column {physical} of {} is not a carrier child",
                    call.name()
                )
            })?;
        proof = self
            .store
            .project(proof, source)
            .map_err(|error| error.to_string())?;
        self.descend(&args[physical], rest, proof)
    }
}

#[derive(Clone, Copy)]
struct SourceGlobal {
    command: usize,
    lhs: TermId,
    rhs: TermId,
    certificate: Option<ProofId>,
}

struct GlobalCursor<'a> {
    native: Option<std::vec::IntoIter<(usize, usize)>>,
    source: std::slice::Iter<'a, ResolvedNCommand>,
    unions: std::slice::Iter<'a, super::super::context::Union>,
    certificates: std::slice::Iter<'a, ProofId>,
    current: Option<(usize, SourceGlobal)>,
}

impl<'a> GlobalCursor<'a> {
    fn new(
        program: &'a ProofContext,
        source: &'a super::super::ResolvedSlottedProgram,
        certificates: &'a [ProofId],
    ) -> Self {
        Self {
            native: None,
            source: source.commands.iter(),
            unions: program.unions.iter(),
            certificates: certificates.iter(),
            current: None,
        }
    }

    fn at(
        &mut self,
        native: &[ResolvedNCommand],
        selected: usize,
        program: &ProofContext,
        store: &SlottedProofStore,
    ) -> LiftResult<SourceGlobal> {
        if let Some((at, global)) = self.current {
            if at == selected {
                return Ok(global);
            }
            if at > selected {
                return Err("global proof origins are not in action order".into());
            }
        }
        if self.native.is_none() {
            self.native = Some(active_actions(native)?.into_iter());
        }
        loop {
            let (at, command) = self
                .native
                .as_mut()
                .unwrap()
                .next()
                .ok_or("global proof action is outside the active scope")?;
            if at > selected {
                return Err("global proof action is outside the active scope".into());
            }
            let ResolvedNCommand::CoreAction(action) = &native[command] else {
                unreachable!("active_actions contains only actions")
            };
            let terms = match action {
                ResolvedAction::Let(_, _, expr)
                    if program.sorts.contains(expr.output_type().name()) =>
                {
                    let Some(ResolvedAction::Let(_, name, _)) = self.next_source(program) else {
                        return Err(format!(
                            "global binding {at} has no corresponding source binding"
                        ));
                    };
                    let term = program.lets[&name.name];
                    Some((term, term, None))
                }
                ResolvedAction::Union(..) => {
                    if !matches!(self.next_source(program), Some(ResolvedAction::Union(..))) {
                        return Err(format!(
                            "global union {at} has no corresponding source union"
                        ));
                    }
                    let union = self
                        .unions
                        .next()
                        .ok_or("source union has no grounded endpoints")?;
                    Some((union.lhs, union.rhs, None))
                }
                ResolvedAction::Expr(_, ResolvedExpr::Call(_, call, _))
                    if call.name().starts_with("Equated_") =>
                {
                    let proof = *self
                        .certificates
                        .next()
                        .ok_or("substitution action has no earlier input certificate")?;
                    let proposition = store.proposition(proof);
                    Some((proposition.lhs, proposition.rhs, Some(proof)))
                }
                _ => None,
            };
            if at == selected {
                let (lhs, rhs, certificate) =
                    terms.ok_or("global proof action has no source occurrence")?;
                let global = SourceGlobal {
                    command,
                    lhs,
                    rhs,
                    certificate,
                };
                self.current = Some((at, global));
                return Ok(global);
            }
        }
    }

    fn next_source(&mut self, program: &ProofContext) -> Option<&'a ResolvedAction> {
        self.source.find_map(|command| match command {
            ResolvedNCommand::CoreAction(action @ ResolvedAction::Let(_, _, expr))
                if program.sorts.contains(expr.output_type().name()) =>
            {
                Some(action)
            }
            ResolvedNCommand::CoreAction(action @ ResolvedAction::Union(..)) => Some(action),
            _ => None,
        })
    }
}

fn active_actions(program: &[ResolvedNCommand]) -> LiftResult<Vec<(usize, usize)>> {
    let mut active = Vec::new();
    let mut scopes = Vec::new();
    let mut next = 0;
    for (index, command) in program.iter().enumerate() {
        match command {
            ResolvedNCommand::CoreAction(_) => {
                active.push((next, index));
                next += 1;
            }
            ResolvedNCommand::Push(count) => {
                scopes.extend(std::iter::repeat_n(active.len(), *count))
            }
            ResolvedNCommand::Pop(_, count) => {
                for _ in 0..*count {
                    active.truncate(scopes.pop().ok_or("unbalanced proof program scope")?);
                }
            }
            _ => {}
        }
    }
    Ok(active)
}
