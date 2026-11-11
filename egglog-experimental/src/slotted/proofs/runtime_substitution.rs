//! Substitution phase certificates. Inputs are certified before any result is
//! inserted; the certificates follow the e-graph through clone and push/pop.

use super::context::{ColumnKind, ProofContext};
use super::format::SlottedProofStore;
use super::lift_slots::source::Certificates;
use super::pipeline::error;
use crate::slotted::rewrite::SubstitutionRequest;
use egglog::proof::RecordedProofs;
use egglog::{CommandOutput, EGraph, Error, Term, TermDag, TermId};
use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

/// Ordinary proofs of substitution inputs, retained for later source proof requests.
#[derive(Clone, Debug, Default)]
pub(in crate::slotted) struct Evidence {
    batches: Vec<Batch>,
    completed: BTreeSet<String>,
}

#[derive(Clone, Debug)]
struct Batch {
    proofs: Arc<RecordedProofs>,
    requests: Vec<String>,
}

impl Evidence {
    pub(super) fn lift(
        &self,
        graph: &EGraph,
        program: &ProofContext,
        source: &super::ResolvedSlottedProgram,
        dag: TermDag,
        names: &super::pipeline::EncodingNames,
    ) -> Result<Certificates, String> {
        let mut certificates = Certificates {
            store: SlottedProofStore::new(dag),
            roots: Vec::new(),
            anchors: super::HashMap::default(),
            head_supports: super::HashMap::default(),
        };
        for (index, batch) in self.batches.iter().enumerate() {
            log::debug!(
                "lifting substitution batch {index}: {} requests",
                batch.requests.len()
            );
            let mut source =
                super::lift_slots::source::SourceLifter::new(program, source, names, &certificates);
            let (proofs, roots) = batch
                .proofs
                .lift_with_visitor(graph, &mut |store, id, origin| {
                    source.visit(store, id, origin)
                });
            certificates = source.finish()?;
            let requests: Vec<_> = roots
                .into_iter()
                .zip(batch.requests.iter().map(String::as_str))
                .collect();
            let (store, ids) = super::lift_slots::substitution_instances(
                program,
                certificates.store.term_dag.clone(),
                names,
                super::lift_slots::NativeProofs {
                    store: &proofs,
                    program: batch.proofs.checking_program(graph),
                },
                &requests,
                &certificates,
            )?;
            certificates.store = store;
            certificates.roots.extend(ids);
            certificates.anchors.clear();
            certificates.head_supports.clear();
        }
        Ok(certificates)
    }
}

#[derive(Clone, Debug)]
pub(in crate::slotted) struct Phase {
    pub substitutions: Vec<SubstitutionRequest>,
}

struct SelectedOutput {
    input: (TermId, egglog::ArcSort),
    request: usize,
    row: String,
    action: String,
}

impl Phase {
    pub(in crate::slotted) fn run(&self, graph: &mut EGraph) -> Result<Vec<CommandOutput>, Error> {
        let layouts = crate::slotted::layout::Layouts::load(graph).map_err(error)?;
        let mut representatives = BTreeMap::new();
        for request in &self.substitutions {
            if representatives.contains_key(&request.sort) {
                continue;
            }
            let symbols = layouts
                .carriers
                .iter()
                .find(|carrier| carrier.sort == request.sort)
                .unwrap();
            representatives.insert(
                request.sort.clone(),
                crate::slotted::runtime::subst::Representatives::new(graph, &symbols.free_vars)
                    .map_err(error)?,
            );
        }
        let mut outputs =
            graph.parse_and_run_program(None, "(run-schedule (run slotted-subst-apply))")?;
        let mut terms = TermDag::default();
        let mut evidence = graph
            .extension_state::<Evidence>()
            .cloned()
            .unwrap_or_default();
        let mut actions = Vec::new();
        let mut selected = Vec::new();
        // Evaluation needs only constructor signatures and binding scopes.
        let source = ProofContext {
            constructors: layouts.constructors.clone().into_iter().collect(),
            ..Default::default()
        };
        for (index, request) in self.substitutions.iter().enumerate() {
            let mut rows = Vec::new();
            graph.constructor_enodes(&request.relation, |row| {
                rows.push(row.children.to_vec());
            })?;
            rows.sort();
            for row in rows {
                let mut arguments = Vec::new();
                for (value, sort) in row.into_iter().zip(&request.columns) {
                    let term = if sort == &request.sort {
                        representatives
                            .get_mut(sort)
                            .unwrap()
                            .term(&mut terms, value)
                            .map_err(error)?
                    } else {
                        let ty = graph.get_sort_by_name(sort).unwrap().clone();
                        let (other, term, _) = graph.extract_value(&ty, value)?;
                        let term = copy_term(&mut terms, &other, term);
                        if sort == "Frame" {
                            terms.app("frame-from-json".into(), vec![term])
                        } else {
                            term
                        }
                    };
                    arguments.push(term);
                }
                let root = arguments[request.root_column];
                let term = terms.app(request.relation.clone(), arguments.clone());
                let row = terms.to_string(term);
                actions.push(format!("(delete {row})"));
                if evidence.completed.contains(&row) {
                    continue;
                }
                let sort = graph
                    .get_function(&request.relation)
                    .unwrap()
                    .func_type()
                    .output()
                    .clone();
                let frame = crate::slotted::runtime::frame_from_term(
                    &terms,
                    match terms.get(arguments[0]) {
                        Term::App(_, args) => args[0],
                        _ => arguments[0],
                    },
                )
                .ok_or_else(|| error("substitution request has no frame"))?;
                let input = [&request.body, &request.replacement].map(|(name, column)| {
                    Ok::<_, Error>((
                        arguments[*column],
                        frame
                            .ren(name)
                            .ok_or_else(|| error("missing substitution input frame"))?
                            .into_iter()
                            .collect(),
                    ))
                });
                let [body, replacement] = input;
                let slot = frame
                    .ren(&request.slot)
                    .and_then(|r| r.get(&0).copied())
                    .ok_or_else(|| error("missing substitution slot"))?;
                let back = frame
                    .ren(&request.root)
                    .ok_or_else(|| error("missing substitution root frame"))?;
                let (mut dag, inputs) = crate::slotted::extract::decode_terms(
                    &terms,
                    &layouts,
                    &[body?, replacement?],
                    back.values().copied().chain([slot]),
                )?;
                let result =
                    super::substitution::substitute(&source, &mut dag, inputs[0], slot, inputs[1])
                        .map_err(error)?;
                let output = encode(&source, &dag, result)?;
                let back = map(back.into_iter().map(|(a, b)| (b, a)));
                let symbols = layouts
                    .carriers
                    .iter()
                    .find(|c| c.sort == request.sort)
                    .unwrap();
                let action = format!(
                    "({} {} {back} {output})",
                    symbols.equated,
                    terms.to_string(root)
                );
                selected.push(SelectedOutput {
                    input: (term, sort),
                    request: index,
                    row,
                    action,
                });
            }
        }
        if !selected.is_empty() {
            // Freeze the input evidence before inserting any result. Later proof
            // reconstruction cannot accidentally use the substitution to justify
            // its own inputs.
            let roots: Vec<_> = selected.iter().map(|output| output.input.clone()).collect();
            log::debug!("recording {} substitution requests", roots.len());
            let proofs = graph.record_existing_terms(&terms, &roots)?;
            let requests = selected
                .into_iter()
                .map(|output| {
                    evidence.completed.insert(output.row);
                    actions.push(output.action);
                    self.substitutions[output.request].name.clone()
                })
                .collect();
            evidence.batches.push(Batch {
                proofs: Arc::new(proofs),
                requests,
            });
        }
        *graph.extension_state_or_default::<Evidence>() = evidence;
        outputs.extend(graph.parse_and_run_program(None, "(run-schedule (run slotted-apply))")?);
        outputs.extend(graph.parse_and_run_program(None, &actions.join("\n"))?);
        Ok(outputs)
    }
}

fn copy_term(to: &mut TermDag, from: &TermDag, root: TermId) -> TermId {
    let mut ids = Vec::with_capacity(from.size());
    for i in 0..from.size() {
        ids.push(match from.get(i) {
            Term::Lit(value) => to.lit(value.clone()),
            Term::Var(name) => to.var(name.clone()),
            Term::App(head, args) => to.app(head.clone(), args.iter().map(|id| ids[*id]).collect()),
        });
    }
    ids[root]
}

fn map(pairs: impl IntoIterator<Item = (i64, i64)>) -> String {
    format!(
        "(map-of {})",
        pairs
            .into_iter()
            .flat_map(|(a, b)| [a.to_string(), b.to_string()])
            .collect::<Vec<_>>()
            .join(" ")
    )
}

/// Encode the evaluated source result in its selected frame. Each child
/// keeps its own free names; binder markers are rigid singleton maps.
fn encode(context: &ProofContext, dag: &TermDag, term: TermId) -> Result<String, Error> {
    let Term::App(head, args) = dag.get(term) else {
        return Err(error("substitution result is not a carrier term"));
    };
    let op = context
        .constructors
        .get(head)
        .ok_or_else(|| error("unknown substitution result constructor"))?;
    let mut columns = Vec::new();
    for (&arg, column) in args.iter().zip(&op.columns) {
        match column {
            ColumnKind::Child => {
                columns.push(map(context
                    .free_slots(dag, arg)
                    .into_iter()
                    .map(|s| (s, s))));
                columns.push(encode(context, dag, arg)?);
            }
            ColumnKind::Var | ColumnKind::Binder => {
                let slot = super::terms::slot_of(dag, arg)
                    .ok_or_else(|| error("invalid substitution result slot"))?;
                columns.push(format!("(map-of 0 {slot})"));
            }
            ColumnKind::Payload(_) => columns.push(dag.to_string(arg)),
        }
    }
    Ok(format!("({head} {})", columns.join(" ")))
}
