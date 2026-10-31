//! Source recording and checked proof extraction for `prove-slotted` commands.

use super::HashMap;
use super::checker::check_claim;
use super::format::SlottedConclusion;
use super::lift_slots::{self, matched_frame};
use super::source::{SlottedProgram, SourceError};
use super::terms::FreshSlots;
use crate::slotted::Compiler;
use crate::slotted::flatten::Rewrite as FlatRewrite;
use crate::slotted::query::ProofNames;
use egglog::TermDag;
use egglog::ast::{
    Command, Expr, Fact, GenericAction, Literal, Macro, ParseError, Parser, Sexp, Span,
};
use egglog::proof::{ProofId, ProofStore};
use egglog::{CommandOutput, EGraph, Error, UserDefinedCommand};
use std::collections::BTreeMap;
use std::fmt::{self, Display, Formatter};
use std::sync::Arc;

#[derive(Debug)]
struct SlottedClaim {
    kind: String,
    lhs: Expr,
    lhs_root: String,
    rhs: Expr,
    rhs_root: String,
    slot_names: BTreeMap<String, i64>,
    names: ProofNames,
}

impl Display for SlottedClaim {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "({} {} {})", self.kind, self.lhs, self.rhs)
    }
}

pub(crate) fn register(graph: &mut EGraph) {
    graph
        .add_command("slotted-prove".into(), Arc::new(ProveSlotted))
        .unwrap();
    graph.parser.add_command_macro(Arc::new(ProveSlotted));
    graph
        .add_command("slotted-record-source".into(), Arc::new(RecordSource))
        .unwrap();
    graph.parser.add_command_macro(Arc::new(RecordSource));
}

fn error(message: impl Display) -> Error {
    Error::ParseError(ParseError(
        egglog::span!(),
        format!("slotted proof: {message}"),
    ))
}

// Extension commands receive Expr arguments. These functions transport syntax
// without evaluating it, including empty lists such as an empty :when clause.
fn datum(source: &Sexp) -> Expr {
    match source {
        Sexp::Atom(name, span) => Expr::Call(
            span.clone(),
            "slotted-source-atom".into(),
            vec![Expr::Lit(span.clone(), Literal::String(name.clone()))],
        ),
        Sexp::Literal(lit, span) => Expr::Lit(span.clone(), lit.clone()),
        Sexp::List(items, span) => Expr::Call(
            span.clone(),
            "slotted-source-list".into(),
            items.iter().map(datum).collect(),
        ),
    }
}

fn source_datum(expr: &Expr) -> Result<Sexp, Error> {
    Ok(match expr {
        Expr::Call(span, head, args) if head == "slotted-source-atom" => {
            let [Expr::Lit(_, Literal::String(name))] = args.as_slice() else {
                return Err(error("invalid source atom"));
            };
            Sexp::Atom(name.clone(), span.clone())
        }
        Expr::Lit(span, lit) => Sexp::Literal(lit.clone(), span.clone()),
        Expr::Call(span, head, args) if head == "slotted-source-list" => Sexp::List(
            args.iter().map(source_datum).collect::<Result<_, _>>()?,
            span.clone(),
        ),
        _ => return Err(error("invalid source datum")),
    })
}

struct RecordSource;

impl Macro<Vec<Command>> for RecordSource {
    fn name(&self) -> &str {
        "slotted-source"
    }

    fn parse(&self, args: &[Sexp], span: Span, _: &mut Parser) -> Result<Vec<Command>, ParseError> {
        let (nested, source) = match args {
            [source] => (false, source),
            [Sexp::Atom(option, _), source] if option == ":no-aliasing" => (true, source),
            _ => {
                return Err(ParseError(
                    span,
                    "expected (slotted-source [:no-aliasing] command)".into(),
                ));
            }
        };
        Ok(vec![Command::UserDefined(
            span.clone(),
            "slotted-record-source".into(),
            vec![Expr::Lit(span, Literal::Bool(nested)), datum(source)],
        )])
    }
}

impl UserDefinedCommand for RecordSource {
    fn supports_proofs(&self) -> bool {
        true
    }

    fn update(&self, graph: &mut EGraph, args: &[Expr]) -> Result<Vec<CommandOutput>, Error> {
        let [Expr::Lit(_, Literal::Bool(nested)), source] = args else {
            return Err(error("invalid source record"));
        };
        let state = graph.extension_state_or_default::<SlottedProofState>();
        let (command, flat) = state
            .compiler
            .retain_source(source_datum(source)?, *nested)
            .map_err(error)?;
        if let Some(flat) = flat {
            state.names.rules.insert(flat.rule.name.clone(), flat);
        }
        state.sources.push(command);
        Ok(vec![])
    }
}

struct ProveSlotted;

impl Macro<Vec<Command>> for ProveSlotted {
    fn name(&self) -> &str {
        "prove-slotted"
    }

    fn parse(
        &self,
        args: &[Sexp],
        span: Span,
        parser: &mut Parser,
    ) -> Result<Vec<Command>, ParseError> {
        let bad = || {
            ParseError(
                span.clone(),
                "expected (prove-slotted (<kind> (lhs root) (rhs root) \"slot names\" \"query names\") facts...)"
                    .into(),
            )
        };
        let Some((Sexp::List(claim, _), facts)) = args.split_first() else {
            return Err(bad());
        };
        let [
            Sexp::Atom(kind, _),
            Sexp::List(lhs, _),
            Sexp::List(rhs, _),
            names @ ..,
        ] = claim.as_slice()
        else {
            return Err(bad());
        };
        let [lhs, Sexp::Atom(lhs_root, _)] = lhs.as_slice() else {
            return Err(bad());
        };
        let [rhs, Sexp::Atom(rhs_root, _)] = rhs.as_slice() else {
            return Err(bad());
        };
        let string = |s: &String| Expr::Lit(span.clone(), Literal::String(s.clone()));
        let mut parsed = vec![
            string(kind),
            datum(lhs),
            string(lhs_root),
            datum(rhs),
            string(rhs_root),
        ];
        let [
            Sexp::Literal(Literal::String(slots), _),
            Sexp::Literal(Literal::String(names), _),
        ] = names
        else {
            return Err(bad());
        };
        parsed.extend([slots, names].map(|s| Expr::Lit(span.clone(), Literal::String(s.clone()))));
        parsed.extend(
            facts
                .iter()
                .map(|f| parser.parse_expr(f))
                .collect::<Result<Vec<_>, _>>()?,
        );
        Ok(vec![Command::UserDefined(
            span,
            "slotted-prove".into(),
            parsed,
        )])
    }
}

impl UserDefinedCommand for ProveSlotted {
    fn supports_proofs(&self) -> bool {
        true
    }

    fn update(&self, graph: &mut EGraph, args: &[Expr]) -> Result<Vec<CommandOutput>, Error> {
        let [
            Expr::Lit(_, Literal::String(kind)),
            lhs,
            Expr::Lit(_, Literal::String(lhs_root)),
            rhs,
            Expr::Lit(_, Literal::String(rhs_root)),
            Expr::Lit(_, Literal::String(slot_names)),
            Expr::Lit(_, Literal::String(names)),
            facts @ ..,
        ] = args
        else {
            return Err(error("invalid slotted claim arguments"));
        };
        let claim = SlottedClaim {
            kind: kind.clone(),
            lhs: crate::slotted::syntax::source_expr(&source_datum(lhs)?)
                .map_err(Error::ParseError)?,
            rhs: crate::slotted::syntax::source_expr(&source_datum(rhs)?)
                .map_err(Error::ParseError)?,
            lhs_root: lhs_root.clone(),
            rhs_root: rhs_root.clone(),
            slot_names: serde_json::from_str(slot_names).map_err(error)?,
            names: serde_json::from_str(names).map_err(error)?,
        };
        let facts = facts
            .iter()
            .map(|f| match f {
                Expr::Call(span, head, args) if head == "=" => match args.as_slice() {
                    [lhs, rhs] => Ok(Fact::Eq(span.clone(), lhs.clone(), rhs.clone())),
                    _ => Err(error("equality facts need two terms")),
                },
                other => Ok(Fact::Fact(other.clone())),
            })
            .collect::<Result<Vec<_>, _>>()?;
        let outputs = graph.run_program(vec![Command::Prove(egglog::span!(), facts)])?;
        let (store, root) = outputs
            .into_iter()
            .find_map(|o| match o {
                CommandOutput::ProveExists {
                    proof_store,
                    proof_id,
                } => Some((proof_store, proof_id)),
                _ => None,
            })
            .ok_or_else(|| error("no existence proof returned"))?;
        let state = graph
            .extension_state::<SlottedProofState>()
            .ok_or_else(|| error("missing slotted source"))?;
        let text = state.prove(&store, root, &claim).map_err(error)?;
        Ok(vec![CommandOutput::UserDefined(Arc::new(text))])
    }
}

/// The generated rule bindings used by reconstruction.
#[derive(Clone, Debug, Default)]
pub(super) struct EncodingNames {
    pub rules: HashMap<String, FlatRewrite>,
}

#[derive(Clone, Default)]
struct SlottedProofState {
    compiler: Compiler,
    names: EncodingNames,
    sources: Vec<Command>,
}

impl SlottedProofState {
    fn program(
        &self,
        slot_names: &BTreeMap<String, i64>,
    ) -> Result<(SlottedProgram, SlottedProgram, TermDag), SourceError> {
        let mut dag = TermDag::default();
        let mut program = SlottedProgram {
            slot_names: slot_names.clone(),
            ..Default::default()
        };
        let language = self.compiler.language();
        let mut flattened = program.clone();
        for source in &self.sources {
            match source {
                Command::Sort { name, .. } => {
                    program.sorts.insert(name.clone());
                    flattened.sorts.insert(name.clone());
                }
                Command::Constructor { name, .. } => {
                    let op = &language.constructors[name];
                    program.constructors.insert(name.clone(), op.clone());
                    flattened.constructors.insert(name.clone(), op.clone());
                }
                Command::Action(GenericAction::Let(_, name, value)) => {
                    program.add_let_expr(&mut dag, name, value)?;
                    flattened.add_let_expr(&mut dag, name, value)?;
                    let term = flattened.refresh_binders(&mut dag, flattened.lets[name]);
                    flattened.lets.insert(name.clone(), term);
                }
                Command::Action(GenericAction::Union(_, a, b)) => {
                    program.add_union_expr(&mut dag, a, b)?;
                    flattened.add_union_expr(&mut dag, a, b)?;
                    let union = flattened.unions.last().unwrap().clone();
                    let lhs = flattened.refresh_binders(&mut dag, union.lhs);
                    let rhs = flattened.refresh_binders(&mut dag, union.rhs);
                    let union = flattened.unions.last_mut().unwrap();
                    union.lhs = lhs;
                    union.rhs = rhs;
                }
                Command::Rewrite(_, rule, false) => {
                    program.add_rewrite_ast(&mut dag, rule)?;
                    flattened.add_rewrite_ast(&mut dag, &self.names.rules[&rule.name].rule)?;
                }
                _ => return Err(SourceError("unsupported retained source command".into())),
            }
        }
        Ok((program, flattened, dag))
    }

    /// Lift the egglog proof `root` of a `prove-slotted` to a slotted proof
    /// of its claim and check it. Returns the slotted proof's text.
    fn prove(
        &self,
        egg: &ProofStore,
        root: ProofId,
        claim: &SlottedClaim,
    ) -> Result<String, String> {
        let (program, flattened, mut dag) =
            self.program(&claim.slot_names).map_err(|e| e.to_string())?;
        let frame = matched_frame(egg, root, &claim.names)?;
        let mut coordinates = BTreeMap::new();
        for &slot in program.slot_names.values() {
            if let Some(coordinate) = frame.node_slot("@globals", slot) {
                coordinates.insert(coordinate, slot);
            }
        }
        let mut fresh = FreshSlots::new(program.slot_names.values().copied());
        let mut query_program = program.clone();
        for name in frame.literal_names() {
            let coordinate = frame
                .ren(&name)
                .and_then(|r| r.get(&0).copied())
                .ok_or_else(|| format!("query slot {name} has no matched coordinate"))?;
            let slot = if let Some(&slot) = coordinates.get(&coordinate) {
                slot
            } else {
                let slot = program
                    .slot_names
                    .get(&name)
                    .copied()
                    .filter(|s| !coordinates.values().any(|v| v == s))
                    .unwrap_or_else(|| fresh.fresh());
                coordinates.insert(coordinate, slot);
                slot
            };
            query_program.slot_names.insert(name, slot);
        }
        // The globals were parsed before assigning query-local slot witnesses.
        let source = query_program
            .claim_expr(&mut dag, &claim.kind, &claim.lhs, &claim.rhs)
            .map_err(|e| format!("claim {claim}: {e}"))?;
        log::debug!(
            "egglog proof of claim {claim}:\n{}",
            egg.proof_to_string(root)
        );
        let (store, proof) = lift_slots::lift(
            &flattened,
            dag,
            &self.names,
            egg,
            root,
            &source,
            &claim.names,
            [&claim.lhs_root, &claim.rhs_root],
        )
        .map_err(|e| format!("claim {claim}: {e}"))?;
        let (mut store, proof) = super::unflatten::lift(store, &program, proof)?;
        check_claim(&mut store, &program, &source, &proof).map_err(|e| {
            format!(
                "the translated proof does not check: {e}\n{}",
                store.conclusion_to_string(&proof)
            )
        })?;
        let proof = SlottedConclusion {
            proof: store.simplify(proof.proof),
            ..proof
        };
        check_claim(&mut store, &program, &source, &proof)
            .map_err(|e| format!("the normalized proof does not check: {e}"))?;
        Ok(store.conclusion_to_string(&proof))
    }
}

#[cfg(test)]
#[path = "pipeline_tests.rs"]
mod tests;
