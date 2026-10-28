//! Source recording and checked proof extraction for `prove-slotted` commands.

use super::HashMap;
use super::checker::check_claim;
use super::format::SlottedConclusion;
use super::source::{ColumnKind, SlottedProgram, SourceError};
use super::terms::FreshSlots;
use super::translate::{matched_frame, translate};
use crate::slotted::flatten::Rewrite as FlatRewrite;
use crate::slotted::query::ProofNames;
use egglog::TermDag;
use egglog::ast::{
    Command, Expr, Fact, GenericAction, GenericExpr, Literal, Macro, ParseError, Parser, Sexp, Span,
};
use egglog::proof::{ProofId, ProofStore};
use egglog::util::SymbolGen;
use egglog::{CommandMacro, CommandOutput, EGraph, Error, TypeInfo, UserDefinedCommand};
use std::collections::{BTreeMap, BTreeSet};
use std::fmt::{self, Display, Formatter};
use std::sync::Arc;

#[derive(Debug)]
struct SlottedClaim {
    kind: String,
    sort: String,
    lhs: String,
    lhs_root: String,
    rhs: String,
    rhs_root: String,
    slot_names: BTreeMap<String, i64>,
    names: ProofNames,
}

impl Display for SlottedClaim {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "({} {} {} {})", self.kind, self.sort, self.lhs, self.rhs)
    }
}

pub(crate) fn register(graph: &mut EGraph) {
    graph
        .add_command("slotted-prove".into(), Arc::new(ProveSlotted))
        .unwrap();
    graph.parser.add_command_macro(Arc::new(ProveSlotted));
    graph
        .add_command("slotted-record".into(), Arc::new(RecordSource))
        .unwrap();
    graph
        .command_macros_mut()
        .register(Arc::new(SourceMetadata));
}

fn error(message: impl Display) -> Error {
    Error::ParseError(ParseError(
        egglog::span!(),
        format!("slotted proof: {message}"),
    ))
}

struct SourceMetadata;

impl CommandMacro for SourceMetadata {
    fn transform(
        &self,
        command: Command,
        _: &mut SymbolGen,
        _: &TypeInfo,
    ) -> Result<Vec<Command>, Error> {
        let string = |s: &str| Expr::Lit(egglog::span!(), Literal::String(s.into()));
        let args = match &command {
            Command::Action(GenericAction::Set(_, head, args, _))
                if METADATA_TABLES.contains(&head.as_str()) =>
            {
                let mut out = vec![string(head)];
                out.extend(args.clone());
                out
            }
            Command::Constructor { name, schema, .. } if schema.outputs.len() == 1 => {
                let mut out = vec![
                    string("constructor"),
                    string(name),
                    string(&schema.outputs[0]),
                ];
                out.extend(schema.input.iter().map(|s| string(s)));
                out
            }
            _ => return Ok(vec![command]),
        };
        Ok(vec![
            command,
            Command::UserDefined(egglog::span!(), "slotted-record".into(), args),
        ])
    }
}

struct RecordSource;

impl UserDefinedCommand for RecordSource {
    fn supports_term_encoding(&self) -> bool {
        true
    }

    fn update(&self, graph: &mut EGraph, args: &[Expr]) -> Result<Vec<CommandOutput>, Error> {
        let Some((head, args)) = args.split_first() else {
            return Err(error("missing metadata kind"));
        };
        let head = lit_string(head).ok_or_else(|| error("expected metadata kind"))?;
        let state = graph.extension_state_or_default::<SlottedProofState>();
        if head == "constructor" {
            let strings = args
                .iter()
                .map(|a| lit_string(a).ok_or_else(|| error("expected constructor signature")))
                .collect::<Result<Vec<_>, _>>()?;
            let [name, output, inputs @ ..] = strings.as_slice() else {
                return Err(error("missing constructor signature"));
            };
            state
                .signatures
                .insert(name.clone(), (inputs.to_vec(), output.clone()));
        } else if head == "rule-names" {
            let [name, names] = args else {
                return Err(error("expected a rule and its generated names"));
            };
            let name = lit_string(name).ok_or_else(|| error("expected a rule name"))?;
            let names = lit_string(names).ok_or_else(|| error("expected generated names"))?;
            state
                .names
                .rules
                .insert(name, serde_json::from_str(&names).map_err(error)?);
        } else {
            state.record(&head, args).map_err(error)?;
        }
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
                "expected (prove-slotted (<kind> <sort> (\"lhs\" root) (\"rhs\" root) \"slot names\" \"query names\") facts...)"
                    .into(),
            )
        };
        let Some((Sexp::List(claim, _), facts)) = args.split_first() else {
            return Err(bad());
        };
        let [
            Sexp::Atom(kind, _),
            Sexp::Atom(sort, _),
            Sexp::List(lhs, _),
            Sexp::List(rhs, _),
            names @ ..,
        ] = claim.as_slice()
        else {
            return Err(bad());
        };
        let side = |xs: &[Sexp]| -> Result<[String; 2], ParseError> {
            let [Sexp::Literal(Literal::String(text), _), Sexp::Atom(root, _)] = xs else {
                return Err(bad());
            };
            Ok([text.clone(), root.clone()])
        };
        let mut parsed = [kind.clone(), sort.clone()]
            .into_iter()
            .chain(side(lhs)?)
            .chain(side(rhs)?)
            .map(|s| Expr::Lit(span.clone(), Literal::String(s)))
            .collect::<Vec<_>>();
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
    fn supports_term_encoding(&self) -> bool {
        true
    }

    fn update(&self, graph: &mut EGraph, args: &[Expr]) -> Result<Vec<CommandOutput>, Error> {
        let [
            Expr::Lit(_, Literal::String(kind)),
            Expr::Lit(_, Literal::String(sort)),
            Expr::Lit(_, Literal::String(lhs)),
            Expr::Lit(_, Literal::String(lhs_root)),
            Expr::Lit(_, Literal::String(rhs)),
            Expr::Lit(_, Literal::String(rhs_root)),
            Expr::Lit(_, Literal::String(slot_names)),
            Expr::Lit(_, Literal::String(names)),
            facts @ ..,
        ] = args
        else {
            return Err(error("expected eight claim strings followed by facts"));
        };
        let claim = SlottedClaim {
            kind: kind.clone(),
            sort: sort.clone(),
            lhs: lhs.clone(),
            rhs: rhs.clone(),
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

/// One source-level fact the compiler recorded, in program order.
#[derive(Clone, Debug)]
enum Source {
    Let(String, String),
    Union(String, String, String),
    Rule(String, String),
}

/// The physical layout the compiler publishes for a constructor, before it is
/// read into surface columns.
#[derive(Clone, Debug, Default)]
struct RawLayout {
    arity: Option<usize>,
    edges: BTreeSet<usize>,
    binders: BTreeSet<usize>,
    payloads: BTreeSet<usize>,
}

/// The carrier identities and generated rule bindings used by reconstruction.
#[derive(Clone, Debug, Default)]
pub(super) struct EncodingNames {
    /// Surface sort name -> carrier index.
    pub carriers: HashMap<String, i64>,
    pub rules: HashMap<String, FlatRewrite>,
}

impl EncodingNames {
    /// Is this the variable constructor of a registered carrier? A user
    /// constructor that happens to be spelled `SlottedVar_7` is not one unless
    /// carrier 7 exists.
    pub(super) fn is_var_constructor(&self, head: &str) -> bool {
        head.strip_prefix("SlottedVar_")
            .and_then(|n| n.parse::<i64>().ok())
            .is_some_and(|n| self.carriers.values().any(|&i| i == n))
    }
}

#[derive(Clone, Debug, Default)]
struct SlottedProofState {
    names: EncodingNames,
    layouts: HashMap<String, RawLayout>,
    /// Each declared constructor's input and output sorts, as the encoded
    /// program declares them: a child column is a `Renaming` and then its sort.
    signatures: HashMap<String, (Vec<String>, String)>,
    sources: Vec<Source>,
}

const METADATA_TABLES: &[&str] = &[
    "SlottedCarrier",
    "SlottedNodeLayout",
    "SlottedEdgeLayout",
    "SlottedBinderLayout",
    "SlottedPayloadLayout",
    "SlottedRuleSource",
    "SlottedLetSource",
    "SlottedUnionSource",
];

fn lit_string(e: &Expr) -> Option<String> {
    match e {
        GenericExpr::Lit(_, Literal::String(s)) => Some(s.clone()),
        _ => None,
    }
}

fn lit_int(e: &Expr) -> Option<i64> {
    match e {
        GenericExpr::Lit(_, Literal::Int(n)) => Some(*n),
        _ => None,
    }
}

impl SlottedProofState {
    /// Record a top-level `(set (Slotted... args) ())` metadata row.
    fn record(&mut self, head: &str, args: &[Expr]) -> Result<(), SourceError> {
        let bad = || SourceError(format!("malformed metadata row ({head} ...)"));
        let s = |i: usize| args.get(i).and_then(lit_string).ok_or_else(bad);
        let n = |i: usize| args.get(i).and_then(lit_int).ok_or_else(bad);
        match head {
            "SlottedCarrier" => {
                self.names.carriers.insert(s(0)?, n(1)?);
            }
            "SlottedNodeLayout" => {
                let arity = usize::try_from(n(1)?).map_err(|_| bad())?;
                self.layouts.entry(s(0)?).or_default().arity = Some(arity);
            }
            "SlottedEdgeLayout" => {
                let edge = usize::try_from(n(1)?).map_err(|_| bad())?;
                self.layouts.entry(s(0)?).or_default().edges.insert(edge);
            }
            "SlottedBinderLayout" => {
                let edge = usize::try_from(n(1)?).map_err(|_| bad())?;
                self.layouts.entry(s(0)?).or_default().binders.insert(edge);
            }
            "SlottedPayloadLayout" => {
                let col = usize::try_from(n(1)?).map_err(|_| bad())?;
                self.layouts.entry(s(0)?).or_default().payloads.insert(col);
            }
            "SlottedRuleSource" => self.sources.push(Source::Rule(s(0)?, s(1)?)),
            "SlottedLetSource" => self.sources.push(Source::Let(s(0)?, s(1)?)),
            "SlottedUnionSource" => self.sources.push(Source::Union(s(0)?, s(1)?, s(2)?)),
            _ => return Err(SourceError(format!("unknown metadata {head}"))),
        }
        Ok(())
    }

    /// The source program as recorded so far, over a fresh term dag.
    fn program(
        &self,
        slot_names: &BTreeMap<String, i64>,
    ) -> Result<(SlottedProgram, SlottedProgram, TermDag), SourceError> {
        let mut dag = TermDag::default();
        let mut program = SlottedProgram {
            slot_names: slot_names.clone(),
            ..Default::default()
        };
        for (name, layout) in &self.layouts {
            if self.names.is_var_constructor(name) {
                continue;
            }
            let arity = layout
                .arity
                .ok_or_else(|| SourceError(format!("constructor {name} has no node layout")))?;
            let (inputs, output) = self
                .signatures
                .get(name)
                .ok_or_else(|| SourceError(format!("constructor {name} was never declared")))?;
            if inputs.len() != arity {
                return Err(SourceError(format!(
                    "constructor {name} is declared with {} columns, its layout has {arity}",
                    inputs.len()
                )));
            }
            let mut columns = vec![];
            let mut i = 0;
            while i < arity {
                if layout.edges.contains(&i) {
                    let kind = if layout.binders.contains(&i) {
                        ColumnKind::Binder
                    } else {
                        ColumnKind::Child
                    };
                    // the edge's renaming, then the child's sort
                    let sort = inputs.get(i + 1).cloned().ok_or_else(|| {
                        SourceError(format!("constructor {name}: edge {i} has no class column"))
                    })?;
                    columns.push((kind, sort));
                    i += 2;
                } else if layout.payloads.contains(&i) {
                    columns.push((ColumnKind::Payload, inputs[i].clone()));
                    i += 1;
                } else {
                    return Err(SourceError(format!(
                        "constructor {name}: physical column {i} is neither an edge nor a payload"
                    )));
                }
            }
            program.add_sorted_constructor(name, output, columns);
        }
        let mut flattened = program.clone();
        for source in &self.sources {
            match source {
                Source::Let(name, text) => {
                    program.add_let(&mut dag, name, text)?;
                    flattened.add_let(&mut dag, name, text)?;
                }
                Source::Union(a, b, sort) => {
                    program.add_union(&mut dag, a, b, sort)?;
                    flattened.add_union(&mut dag, a, b, sort)?;
                }
                Source::Rule(name, text) => {
                    program.add_named_rewrite(&mut dag, Some(name), text)?;
                    let rule =
                        self.names.rules.get(name).ok_or_else(|| {
                            SourceError(format!("missing flattened rewrite {name}"))
                        })?;
                    flattened.add_named_rewrite(&mut dag, Some(name), &rule.source)?;
                }
            }
        }
        Ok((program, flattened, dag))
    }

    /// Translate the egglog proof `root` of a `prove-slotted` to a slotted proof
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
            .claim(&mut dag, &claim.kind, &claim.sort, &claim.lhs, &claim.rhs)
            .map_err(|e| format!("claim {claim}: {e}"))?;
        log::debug!(
            "egglog proof of claim {claim}:\n{}",
            egg.proof_to_string(root)
        );
        let (store, proof) = translate(
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
mod tests {
    use super::*;
    use crate::slotted::{Compiler, Options, ProofMode, new_egraph_with_proofs};

    #[test]
    fn restricted_group_elements_lift_to_checked_source_equalities() {
        let mut compiler = Compiler::new(Options {
            proof_mode: ProofMode::Check,
            ..Default::default()
        });
        let encoded = compiler
            .compile(
                None,
                include_str!("../../../tests/slotted/proof-group-restriction.egg"),
            )
            .unwrap();
        let mut graph = new_egraph_with_proofs();
        graph.parse_and_run_program(None, &encoded).unwrap();
        let outputs = graph
            .parse_and_run_program(None, "(prove (= g (EclassGroup_0 c)) (> (set-length g) 1))")
            .unwrap();
        let egg = outputs
            .into_iter()
            .find_map(|output| match output {
                CommandOutput::ProveExists { proof_store, .. } => Some(proof_store),
                _ => None,
            })
            .unwrap();
        let state = graph.extension_state::<SlottedProofState>().unwrap();
        let (program, _, dag) = state.program(&BTreeMap::new()).unwrap();
        let checked =
            super::super::translate::check_restricted_symmetries(&program, dag, &state.names, &egg)
                .unwrap();
        assert!(
            checked > 0,
            "the proof must exercise a nonidentity restricted symmetry"
        );
    }
}
