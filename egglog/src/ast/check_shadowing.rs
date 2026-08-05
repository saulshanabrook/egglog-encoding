use crate::{util::HashMap, util::HashSet, *};

#[derive(Clone, Debug, Default)]
pub(crate) struct Names {
    seen: HashMap<String, Span>,
    global_aliases: HashMap<String, (String, Span)>,
    checked_aliases: HashSet<String>,
}

impl Names {
    #[cfg(test)]
    pub(crate) fn contains_canonical(&self, canonical: &str) -> bool {
        self.seen.contains_key(canonical)
            || self.seen.contains_key(&format!("${canonical}"))
            || self.global_aliases.contains_key(canonical)
    }

    fn check(&mut self, name: String, new: Span) -> Result<(), Error> {
        if let Some(old) = self.seen.get(&name) {
            Err(Error::Shadowing(name, old.clone(), new))
        } else {
            self.seen.insert(name, new);
            Ok(())
        }
    }

    /// Check the checked-alias namespace without publishing the name. Runtime
    /// evaluation may still fail, so committing during resolution would leave a
    /// ghost binding behind.
    pub(crate) fn check_checked_alias_available(
        &self,
        name: &str,
        new: &Span,
    ) -> Result<(), Error> {
        let canonical = name.strip_prefix(GLOBAL_NAME_PREFIX).unwrap_or(name);
        let conflict = self
            .seen
            .get(name)
            .or_else(|| self.seen.get(canonical))
            .or_else(|| self.seen.get(&format!("${canonical}")))
            .or_else(|| self.global_aliases.get(canonical).map(|(_, span)| span));
        if let Some(old) = conflict {
            Err(Error::Shadowing(name.to_owned(), old.clone(), new.clone()))
        } else {
            Ok(())
        }
    }

    /// Publish a successfully evaluated checked alias in both spellings so a
    /// later declaration cannot collide through `$` canonicalization.
    pub(crate) fn record_checked_alias(&mut self, name: &str, span: &Span) {
        let canonical = name.strip_prefix(GLOBAL_NAME_PREFIX).unwrap_or(name);
        debug_assert!(self.check_checked_alias_available(name, span).is_ok());
        self.seen.insert(name.to_owned(), span.clone());
        self.seen.insert(canonical.to_owned(), span.clone());
        self.checked_aliases.insert(name.to_owned());
        self.track_global_alias(name, span);
    }

    fn track_global_alias(&mut self, name: &str, span: &Span) {
        if let Some(stripped) = name.strip_prefix(GLOBAL_NAME_PREFIX) {
            self.global_aliases
                .insert(stripped.to_owned(), (name.to_owned(), span.clone()));
        }
    }

    fn check_pattern_name(&mut self, name: &str, span: &Span) -> Result<(), Error> {
        let canonical = name
            .strip_prefix(GLOBAL_NAME_PREFIX)
            .unwrap_or(name)
            .to_owned();
        if let Some((global_name, global_span)) = self.global_aliases.get(&canonical) {
            return Err(Error::Shadowing(
                format!("pattern variable `{name}` conflicts with global `{global_name}`"),
                global_span.clone(),
                span.clone(),
            ));
        }
        self.check(name.to_owned(), span.clone())
    }

    /// WARNING: this function does not handle `push` and `pop`.
    /// Because `Names` is contained on the `EGraph`, this will
    /// work correctly when executed from `process_command`, but
    /// a unit test that called this function multiple times without
    /// changing the `EGraph` will be wrong.
    pub(crate) fn check_shadowing(&mut self, command: &ResolvedNCommand) -> Result<(), Error> {
        match command {
            ResolvedNCommand::Sort { span, name, .. } => self.check(name.clone(), span.clone()),
            ResolvedNCommand::Function(decl) => {
                self.check(decl.name.clone(), decl.span.clone())?;
                if decl.internal_let {
                    self.track_global_alias(&decl.name, &decl.span);
                }
                Ok(())
            }
            ResolvedNCommand::Index { span, name, .. } => self.check(name.clone(), span.clone()),
            ResolvedNCommand::AddRuleset(span, name) => self.check(name.clone(), span.clone()),
            ResolvedNCommand::UnstableCombinedRuleset(span, name, _args) => {
                self.check(name.clone(), span.clone())
            }
            ResolvedNCommand::NormRule { rule, .. } => {
                let mut inner = self.clone();
                inner.check_shadowing_query(&rule.body)?;
                for action in rule.head.iter() {
                    inner.check_shadowing_action(action)?;
                }
                Ok(())
            }
            ResolvedNCommand::CoreAction(action) => self.check_shadowing_action(action),
            ResolvedNCommand::CoreActions(actions) => {
                let mut inner = self.clone();
                for action in actions.iter() {
                    inner.check_shadowing_action(action)?;
                }
                Ok(())
            }
            ResolvedNCommand::LetBegin(..) => {
                unreachable!("LetBegin is removed by remove_globals")
            }
            // Runtime evaluation owns atomic namespace publication.
            ResolvedNCommand::LetCheck { .. } => Ok(()),
            ResolvedNCommand::Check(_span, query) => {
                let mut inner = self.clone();
                inner.check_shadowing_check(query)
            }
            ResolvedNCommand::Fail(_span, commands) => {
                let mut inner = self.clone();
                for command in commands {
                    inner.check_shadowing(command)?;
                }
                Ok(())
            }
            ResolvedNCommand::Extract(..) => Ok(()),
            ResolvedNCommand::RunSchedule(..) => Ok(()),
            ResolvedNCommand::PrintOverallStatistics(..) => Ok(()),
            ResolvedNCommand::ProveExists(..) => Ok(()),
            ResolvedNCommand::PrintFunction(..) => Ok(()),
            ResolvedNCommand::PrintSize(..) => Ok(()),
            ResolvedNCommand::Input { .. } => Ok(()),
            ResolvedNCommand::Output { .. } => Ok(()),
            ResolvedNCommand::Push(..) => Ok(()),
            ResolvedNCommand::Pop(..) => Ok(()),
            ResolvedNCommand::UserDefined(..) => Ok(()),
        }
    }

    fn check_shadowing_query(&mut self, query: &[ResolvedFact]) -> Result<(), Error> {
        self.check_shadowing_query_with(query, |_| false)
    }

    fn check_shadowing_check(&mut self, query: &[ResolvedFact]) -> Result<(), Error> {
        let checked_aliases = self.checked_aliases.clone();
        self.check_shadowing_query_with(query, |name| checked_aliases.contains(name))
    }

    fn check_shadowing_query_with(
        &mut self,
        query: &[ResolvedFact],
        is_checked_alias: impl Fn(&str) -> bool,
    ) -> Result<(), Error> {
        // we want to allow names in queries to shadow each other, so we first collect
        // all of the variable names, and then we check each of those names once
        fn collect_expr_names(expr: &ResolvedExpr, out: &mut HashMap<String, Span>) {
            match expr {
                ResolvedExpr::Lit(..) => {}
                ResolvedExpr::Var(span, name) => {
                    out.entry(name.name.clone()).or_insert_with(|| span.clone());
                }
                ResolvedExpr::Call(_span, _func, args) => {
                    args.iter().for_each(|e| collect_expr_names(e, out));
                }
            }
        }

        let mut collected = HashMap::default();

        for fact in query {
            match fact {
                ResolvedFact::Eq(_span, e1, e2) => {
                    collect_expr_names(e1, &mut collected);
                    collect_expr_names(e2, &mut collected);
                }
                ResolvedFact::Fact(e) => collect_expr_names(e, &mut collected),
            }
        }

        for (name, span) in collected {
            if !is_checked_alias(&name) {
                self.check_pattern_name(&name, &span)?;
            }
        }

        Ok(())
    }

    fn check_shadowing_action(&mut self, action: &ResolvedAction) -> Result<(), Error> {
        if let ResolvedAction::Let(span, name, _args) = action {
            self.check_pattern_name(&name.name, span)
        } else {
            Ok(())
        }
    }
}
