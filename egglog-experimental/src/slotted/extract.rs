//! Tree extraction with source constructors and capture-avoiding slot names.
use std::collections::{BTreeMap, BTreeSet};

use egglog::{
    ArcSort, CommandOutput, EGraph, Enode, Error, Function, Term, TermDag, TermId,
    UserDefinedCommand, Value,
    ast::{Expr, Literal},
    extract::TreeCostModel,
    sort::MapContainer,
};
use num::{BigUint, ToPrimitive};

use super::{layout::Layouts, model::Column};

type Frame = BTreeMap<i64, String>;

/// Count source constructors and variable occurrences, excluding binder markers,
/// renamings, and payloads. Exact costs keep every term larger than its children.
struct TreeSize<'a>(&'a Layouts);

impl TreeCostModel<BigUint> for TreeSize<'_> {
    type EnodeCost = Vec<usize>;
    type ContainerCost = ();

    fn base_value_cost(&self, _: &EGraph, _: &ArcSort, _: Value) -> BigUint {
        BigUint::default()
    }

    fn enode_cost(&self, _: &EGraph, function: &Function, _: &Enode<'_>) -> Vec<usize> {
        let mut children = Vec::new();
        if let Some(op) = self.0.constructors.get(function.name()) {
            let mut physical = 0;
            for column in &op.columns {
                if *column == Column::Child {
                    children.push(physical + 1);
                }
                physical += if matches!(column, Column::Payload(_)) {
                    1
                } else {
                    2
                };
            }
        }
        children
    }

    fn container_cost(&self, _: &EGraph, _: &ArcSort, _: Value) {}

    fn fold_enode_cost(&self, children: Vec<usize>, costs: &[BigUint]) -> BigUint {
        children
            .into_iter()
            .fold(BigUint::from(1u8), |cost, i| cost + &costs[i])
    }

    fn fold_container_cost(&self, _: (), _: &[BigUint]) -> BigUint {
        BigUint::default()
    }
}

fn error(message: impl Into<String>) -> Error {
    Error::BackendError(format!("slotted extraction: {}", message.into()))
}

fn renaming(graph: &EGraph, value: Value) -> Result<BTreeMap<i64, i64>, Error> {
    let map = graph
        .value_to_container::<MapContainer>(value)
        .ok_or_else(|| error("expected a slot renaming"))?;
    Ok(map
        .data
        .iter()
        .map(|(a, b)| {
            (
                graph.value_to_base::<i64>(*a),
                graph.value_to_base::<i64>(*b),
            )
        })
        .collect())
}

struct Decoder<'a> {
    encoded: &'a TermDag,
    layouts: &'a Layouts,
    output: TermDag,
    used: BTreeSet<String>,
    next: usize,
    memo: BTreeMap<(TermId, Frame), TermId>,
}

impl Decoder<'_> {
    fn fresh(&mut self) -> String {
        loop {
            let name = format!("${}", self.next);
            self.next += 1;
            if self.used.insert(name.clone()) {
                return name;
            }
        }
    }

    fn name(&mut self, frame: &mut Frame, slot: i64) -> String {
        frame.entry(slot).or_insert_with(|| self.fresh()).clone()
    }

    fn edge(&self, id: TermId) -> Result<BTreeMap<i64, i64>, Error> {
        let Term::App(op, args) = self.encoded.get(id) else {
            return Err(error("expected an extracted renaming"));
        };
        if op != "map-of" || !args.len().is_multiple_of(2) {
            return Err(error("expected an extracted map-of"));
        }
        args.chunks_exact(2)
            .map(
                |pair| match (self.encoded.get(pair[0]), self.encoded.get(pair[1])) {
                    (Term::Lit(Literal::Int(a)), Term::Lit(Literal::Int(b))) => Ok((*a, *b)),
                    _ => Err(error("renaming entries must be integer slots")),
                },
            )
            .collect()
    }

    fn term(&mut self, id: TermId, mut frame: Frame) -> Result<TermId, Error> {
        let key = (id, frame.clone());
        if let Some(&result) = self.memo.get(&key) {
            return Ok(result);
        }
        let Term::App(name, args) = self.encoded.get(id) else {
            return Err(error("expected a constructor term"));
        };
        let result = if self.layouts.carriers.iter().any(|s| s.var == *name) {
            let [slot] = args.as_slice() else {
                return Err(error("invalid variable constructor"));
            };
            let Term::Lit(Literal::Int(slot)) = self.encoded.get(*slot) else {
                return Err(error("invalid variable slot"));
            };
            let name = self.name(&mut frame, *slot);
            self.output.var(name)
        } else {
            let op = self
                .layouts
                .constructors
                .get(name)
                .ok_or_else(|| error(format!("unknown constructor {name}")))?;
            let mut physical = 0;
            let mut edges = Vec::new();
            let mut binders = BTreeMap::new();
            for column in &op.columns {
                if matches!(column, Column::Payload(_)) {
                    physical += 1;
                } else {
                    let edge = self.edge(args[physical])?;
                    if *column == Column::Binder {
                        let slot = *edge.get(&0).ok_or_else(|| error("binder lacks its slot"))?;
                        binders.insert(slot, self.fresh());
                    }
                    edges.push(edge);
                    physical += 2;
                }
            }
            let mut children = Vec::new();
            let mut child = 0;
            physical = 0;
            for column in &op.columns {
                match column {
                    Column::Payload(_) => {
                        let Term::Lit(value) = self.encoded.get(args[physical]) else {
                            return Err(error("expected a literal payload"));
                        };
                        children.push(self.output.lit(value.clone()));
                        physical += 1;
                    }
                    Column::Binder => {
                        children.push(self.output.var(binders[&edges[child][&0]].clone()));
                        physical += 2;
                        child += 1;
                    }
                    Column::Child => {
                        let mut child_frame = Frame::new();
                        for (&from, &to) in &edges[child] {
                            let bound = (Some(child) == op.covered())
                                .then(|| binders.get(&to))
                                .flatten();
                            let name = bound.cloned().unwrap_or_else(|| self.name(&mut frame, to));
                            child_frame.insert(from, name);
                        }
                        children.push(self.term(args[physical + 1], child_frame)?);
                        physical += 2;
                        child += 1;
                    }
                }
            }
            self.output.app(name.clone(), children)
        };
        self.memo.insert(key, result);
        Ok(result)
    }
}

/// Evaluate the compiler's prepared root after maintenance and decode its best tree.
pub(super) struct ExtractCommand;

impl UserDefinedCommand for ExtractCommand {
    fn update(&self, graph: &mut EGraph, args: &[Expr]) -> Result<Vec<CommandOutput>, Error> {
        let [root, frame, names @ ..] = args else {
            return Err(error("expected a term and its slot frame"));
        };
        let (sort, root) = graph.eval_expr(root)?;
        let (_, frame) = graph.eval_expr(frame)?;
        let frame = renaming(graph, frame)?;
        let mut source_names = BTreeMap::new();
        for name in names {
            let Expr::Call(_, _, args) = name else {
                return Err(error("expected a slot name"));
            };
            let [
                Expr::Lit(_, Literal::Int(id)),
                Expr::Lit(_, Literal::String(name)),
            ] = args.as_slice()
            else {
                return Err(error("expected a slot ID and spelling"));
            };
            source_names.insert(*id, name.clone());
        }
        let layouts = Layouts::load(graph).map_err(error)?;
        let symbols = layouts
            .carriers
            .iter()
            .find(|s| s.sort == sort.name())
            .ok_or_else(|| error("root is not a slotted term"))?;
        let mut leaders = Vec::new();
        graph.constructor_enodes(&symbols.renames, |row| {
            if row.children[0] == root {
                leaders.push((row.children[2], row.children[1]));
            }
        })?;
        let (leader, ren) = leaders
            .into_iter()
            .min()
            .ok_or_else(|| error("term has no maintained leader"))?;
        let mut initial = Frame::new();
        for (from, to) in renaming(graph, ren)? {
            let name = frame
                .get(&to)
                .and_then(|s| source_names.get(s))
                .ok_or_else(|| error("leader slot is missing its source name"))?;
            initial.insert(from, name.clone());
        }
        let mut extracted =
            graph.extract_best_with_cost_model(vec![(sort, leader)], TreeSize(&layouts))?;
        let best = extracted
            .terms
            .pop()
            .flatten()
            .ok_or_else(|| error("term has no finite tree representative"))?;
        let mut decoder = Decoder {
            encoded: &extracted.termdag,
            layouts: &layouts,
            output: TermDag::default(),
            used: source_names.into_values().collect(),
            next: 0,
            memo: BTreeMap::new(),
        };
        let term = decoder.term(best.term, initial)?;
        Ok(vec![CommandOutput::ExtractBest(
            decoder.output,
            best.cost.to_u64().unwrap_or(u64::MAX),
            term,
        )])
    }
}
