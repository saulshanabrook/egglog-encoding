//! Compiled commands and the source programs used to check their proofs.

use super::proofs::pipeline::{ProofRequest, error};
use egglog::ast::{Command, Expr, Fact, Literal};
use egglog::{CommandOutput, EGraph, Error};
use std::collections::BTreeMap;
use std::fmt::{self, Display, Formatter};
use std::sync::Arc;

pub(super) type ProofRequests = BTreeMap<usize, Arc<ProofRequest>>;

#[derive(Clone)]
pub(super) struct ExtractRequest {
    pub compiler: super::Compiler,
    pub input: String,
}

impl fmt::Debug for ExtractRequest {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        f.debug_struct("ExtractRequest")
            .field("input", &self.input)
            .finish_non_exhaustive()
    }
}

pub(super) type ExtractRequests = BTreeMap<usize, Arc<ExtractRequest>>;

/// Lowered slotted commands with their original checking programs.
/// Use [`Self::run`] to execute them, including source-level proof checking.
/// Display serializes only the lowered commands; proof replay also needs this
/// compilation of the original source.
#[derive(Clone, Debug)]
pub struct CompiledProgram {
    pub(super) commands: Vec<Command>,
    pub(super) proofs: ProofRequests,
    pub(super) extractions: ExtractRequests,
    pub(super) substitutions: BTreeMap<usize, Arc<super::proofs::runtime_substitution::Phase>>,
}

impl Display for CompiledProgram {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        for command in &self.commands {
            writeln!(f, "{command}")?;
        }
        Ok(())
    }
}

impl CompiledProgram {
    /// Execute on a registered slotted e-graph. Proof requests require proof mode.
    pub fn run(&self, graph: &mut EGraph) -> Result<Vec<CommandOutput>, Error> {
        self.run_commands(graph, self.commands.clone())
    }

    /// Run serialized lowered commands using this compilation's checking programs.
    /// The commands must correspond to the same source inputs and compiler options.
    pub fn run_encoded(
        &self,
        graph: &mut EGraph,
        filename: Option<String>,
        encoded: &str,
    ) -> Result<Vec<CommandOutput>, Error> {
        let commands = graph.parse_program(filename, encoded)?;
        self.run_commands(graph, commands)
    }

    /// Associate serialized commands with this compilation's checking programs.
    pub fn with_encoded(&self, filename: Option<String>, encoded: &str) -> Result<Self, Error> {
        let mut graph = super::new_egraph();
        super::proofs::pipeline::register(&mut graph);
        Ok(Self {
            commands: graph.parse_program(filename, encoded)?,
            proofs: self.proofs.clone(),
            extractions: self.extractions.clone(),
            substitutions: self.substitutions.clone(),
        })
    }

    fn run_commands(
        &self,
        graph: &mut EGraph,
        commands: Vec<Command>,
    ) -> Result<Vec<CommandOutput>, Error> {
        let mut outputs = Vec::new();
        let mut pending = Vec::new();
        for command in commands {
            if let Command::UserDefined(_, name, args) = &command
                && name == "slotted-substitute"
            {
                outputs.extend(graph.run_program(std::mem::take(&mut pending))?);
                let [Expr::Lit(_, Literal::Int(id))] = args.as_slice() else {
                    return Err(error("expected (slotted-substitute phase-id)"));
                };
                let phase = usize::try_from(*id)
                    .ok()
                    .and_then(|id| self.substitutions.get(&id))
                    .ok_or_else(|| error(format!("missing substitution phase {id}")))?;
                outputs.extend(phase.run(graph)?);
                continue;
            }
            if let Command::UserDefined(_, name, args) = &command
                && name == "slotted-prove-extract"
            {
                outputs.extend(graph.run_program(std::mem::take(&mut pending))?);
                let [Expr::Lit(_, Literal::Int(id)), args @ ..] = args.as_slice() else {
                    return Err(error(
                        "expected (slotted-prove-extract request-id term frame slots...)",
                    ));
                };
                let request = usize::try_from(*id)
                    .ok()
                    .and_then(|id| self.extractions.get(&id))
                    .ok_or_else(|| error(format!("missing extraction request {id}")))?;
                use egglog::UserDefinedCommand;
                let extracted = super::extract::ExtractCommand.update(graph, args)?;
                let Some(CommandOutput::ExtractBest(dag, _, term)) = extracted.first() else {
                    return Err(error("extraction returned no representative"));
                };
                let check = format!("(check (= {} {}))", request.input, dag.to_string(*term));
                let mut compiler = request.compiler.clone();
                let certificate = compiler.compile_program(None, &check)?.run(graph)?;
                outputs.extend(extracted);
                outputs.extend(certificate);
                continue;
            }
            if let Command::UserDefined(_, name, args) = &command
                && name == "slotted-prove"
            {
                outputs.extend(graph.run_program(std::mem::take(&mut pending))?);
                let [Expr::Lit(_, Literal::Int(id)), facts @ ..] = args.as_slice() else {
                    return Err(error("expected (slotted-prove request-id facts...)"));
                };
                let request = usize::try_from(*id)
                    .ok()
                    .and_then(|id| self.proofs.get(&id))
                    .ok_or_else(|| {
                        error(format!(
                            "missing proof request {id} in the checking program"
                        ))
                    })?;
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
                outputs.extend(request.run(graph, facts)?);
            } else {
                pending.push(command);
            }
        }
        outputs.extend(graph.run_program(pending)?);
        Ok(outputs)
    }
}

#[cfg(feature = "bin")]
impl egglog::CliProgram for CompiledProgram {
    fn run(&self, graph: &mut EGraph, _: Option<String>) -> Result<Vec<CommandOutput>, Error> {
        self.run(graph)
    }

    fn desugar(&self, _: &mut EGraph, _: Option<String>) -> Result<Vec<Command>, Error> {
        Ok(self.commands.clone())
    }
}
