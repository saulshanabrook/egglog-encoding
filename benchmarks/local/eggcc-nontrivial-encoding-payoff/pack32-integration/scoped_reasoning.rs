//! Exact-scope bounded Pack32 experiment. Only the final checked Eq=false
//! leaves the private graph; local field equalities never enter EggCC's graph.
use crate::schema::{Assumption, BaseType, BinaryOp, Constant, Expr, RcExpr, TreeProgram, Type};
use egglog::{new_experimental_egraph_with_options, DisequalityEncoding, Error};
use serde_json::{json, Value};
use std::{
    collections::BTreeSet,
    path::Path,
    sync::atomic::{AtomicUsize, Ordering},
};
const BASE: i64 = 4294967296;
const MASK: i64 = BASE - 1;
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Word {
    Slot(Assumption, usize),
    Constant(i64),
    Add(Box<Word>, Box<Word>),
    Mul(Box<Word>, Box<Word>),
    Mask(Box<Word>, Box<Word>),
}
#[derive(Clone, Debug, PartialEq, Eq)]
enum Transport {
    Slot(usize),
    Unknown,
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum Shape {
    Scalar(Transport),
    Tuple(Vec<Transport>),
}

struct Invariant {
    scope: Assumption,
    index: usize,
    value: i64,
}

/// Expand exact tuple projections and If input bindings. A slot survives an If
/// only when BOTH branches forward that same lexical input slot. Arithmetic is
/// deliberately unknown: even `slot + 0` is outside this structural proof.
fn transport(expr: &RcExpr, scope: &Assumption, input: &[Transport]) -> Option<Shape> {
    match expr.as_ref() {
        Expr::Arg(Type::TupleT(fields), ctx) if ctx == scope && fields.len() == input.len() => {
            Some(Shape::Tuple(input.to_vec()))
        }
        Expr::Get(tuple, index) => {
            let Shape::Tuple(values) = transport(tuple, scope, input)? else {
                return None;
            };
            Some(Shape::Scalar(values.get(*index)?.clone()))
        }
        Expr::Single(value) => {
            let Shape::Scalar(value) = transport(value, scope, input)? else {
                return None;
            };
            Some(Shape::Tuple(vec![value]))
        }
        Expr::Concat(left, right) => {
            let Shape::Tuple(mut values) = transport(left, scope, input)? else {
                return None;
            };
            let Shape::Tuple(right) = transport(right, scope, input)? else {
                return None;
            };
            values.extend(right);
            Some(Shape::Tuple(values))
        }
        Expr::Empty(_, ctx) if ctx == scope => Some(Shape::Tuple(Vec::new())),
        Expr::Const(_, _, ctx) if ctx == scope => Some(Shape::Scalar(Transport::Unknown)),
        Expr::Bop(..) | Expr::Uop(..) | Expr::Top(..) => Some(Shape::Scalar(Transport::Unknown)),
        Expr::If(pred, branch_input, yes, no) => {
            if pred.get_ctx() != scope || branch_input.get_ctx() != scope {
                return None;
            }
            let Shape::Tuple(values) = transport(branch_input, scope, input)? else {
                return None;
            };
            let yes_ctx = Assumption::InIf(true, pred.clone(), branch_input.clone());
            let no_ctx = Assumption::InIf(false, pred.clone(), branch_input.clone());
            match (
                transport(yes, &yes_ctx, &values)?,
                transport(no, &no_ctx, &values)?,
            ) {
                (Shape::Tuple(a), Shape::Tuple(b)) if a.len() == b.len() => Some(Shape::Tuple(
                    a.into_iter()
                        .zip(b)
                        .map(|(x, y)| if x == y { x } else { Transport::Unknown })
                        .collect(),
                )),
                (Shape::Scalar(a), Shape::Scalar(b)) => {
                    Some(Shape::Scalar(if a == b { a } else { Transport::Unknown }))
                }
                _ => None,
            }
        }
        _ => None,
    }
}

/// Induction admitted only for a literal initial projection and unchanged
/// same-index body output. DoWhile body output 0 is its predicate, so slot i is
/// carried by body output i+1. Other-index forwarding and updates are rejected.
fn loop_invariants(program: &TreeProgram) -> Vec<Invariant> {
    let mut stack = vec![program.entry.clone()];
    stack.extend(program.functions.clone());
    let mut seen = BTreeSet::new();
    let mut result = Vec::new();
    while let Some(expr) = stack.pop() {
        if !seen.insert(std::rc::Rc::as_ptr(&expr)) {
            continue;
        }
        stack.extend(expr.children_exprs());
        let Expr::DoWhile(initial, body) = expr.as_ref() else {
            continue;
        };
        let Type::TupleT(fields) = body.get_arg_type() else {
            continue;
        };
        let scope = body.get_ctx();
        let slots = (0..fields.len()).map(Transport::Slot).collect::<Vec<_>>();
        let Some(Shape::Tuple(outputs)) = transport(body, scope, &slots) else {
            continue;
        };
        if outputs.len() != fields.len() + 1 {
            continue;
        }
        for (index, ty) in fields.iter().enumerate() {
            if ty != &BaseType::IntT || outputs[index + 1] != Transport::Slot(index) {
                continue;
            }
            let Some(value) = project(initial, index) else {
                continue;
            };
            let literal = match value.as_ref() {
                Expr::Const(Constant::Int(value), _, ctx) if ctx == initial.get_ctx() => {
                    Some(*value)
                }
                Expr::Get(arg, i) => match arg.as_ref() {
                    Expr::Arg(Type::TupleT(fields), ctx)
                        if ctx == initial.get_ctx() && fields.get(*i) == Some(&BaseType::IntT) =>
                    {
                        constant_slot(ctx, *i, &[])
                    }
                    _ => None,
                },
                _ => None,
            };
            let Some(value) = literal else { continue };
            result.push(Invariant {
                scope: scope.clone(),
                index,
                value,
            });
        }
    }
    result
}

/// Transport a proved loop constant through exact enclosing If inputs.
fn constant_slot(scope: &Assumption, index: usize, invariants: &[Invariant]) -> Option<i64> {
    if let Some(value) = invariants
        .iter()
        .find(|x| x.scope == *scope && x.index == index)
    {
        return Some(value.value);
    }
    let Assumption::InIf(_, _, input) = scope else {
        return None;
    };
    let value = project(input, index)?;
    match value.as_ref() {
        Expr::Const(Constant::Int(k), _, ctx) if ctx == input.get_ctx() => Some(*k),
        Expr::Get(arg, i) => {
            let Expr::Arg(Type::TupleT(fields), ctx) = arg.as_ref() else {
                return None;
            };
            if fields.get(*i) != Some(&BaseType::IntT) || ctx != input.get_ctx() {
                return None;
            }
            constant_slot(ctx, *i, invariants)
        }
        _ => None,
    }
}

fn tuple_length(expr: &RcExpr) -> Option<usize> {
    match expr.as_ref() {
        Expr::Single(_) => Some(1),
        Expr::Concat(a, b) => Some(tuple_length(a)? + tuple_length(b)?),
        Expr::Empty(_, _) => Some(0),
        Expr::Arg(Type::TupleT(fields), _) => Some(fields.len()),
        _ => None,
    }
}

/// Exact structural projection through the branch's declared input tuple.
/// Unsupported expressions remain unknown; they are never treated as fresh values.
fn project(expr: &RcExpr, index: usize) -> Option<RcExpr> {
    match expr.as_ref() {
        Expr::Single(value) if index == 0 => Some(value.clone()),
        Expr::Concat(left, right) => {
            let length = tuple_length(left)?;
            if index < length {
                project(left, index)
            } else {
                project(right, index - length)
            }
        }
        Expr::Arg(Type::TupleT(fields), _) if index < fields.len() => {
            Some(RcExpr::new(Expr::Get(expr.clone(), index)))
        }
        _ => None,
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Mode {
    Off,
    SeedOnly,
    PrimitiveOnly,
    CancellationOff,
    CancellationRescue,
    ReverseOff,
    DisequalityRescue,
    ForwardOff,
    QueryOff,
    Manual,
    Encoding,
    BridgeOff,
    ConsumerOff,
}
impl Mode {
    fn from_env() -> Self {
        match std::env::var("EGGCC_SCOPED_MODE")
            .as_deref()
            .unwrap_or("off")
        {
            "off" => Self::Off,
            "seed-only" => Self::SeedOnly,
            "primitive-only" => Self::PrimitiveOnly,
            "cancellation-off" => Self::CancellationOff,
            "cancellation-rescue" => Self::CancellationRescue,
            "reverse-off" => Self::ReverseOff,
            "disequality-rescue" => Self::DisequalityRescue,
            "forward-off" => Self::ForwardOff,
            "query-off" => Self::QueryOff,
            "manual" => Self::Manual,
            "encoding" => Self::Encoding,
            "bridge-off" => Self::BridgeOff,
            "consumer-off" => Self::ConsumerOff,
            other => panic!("Unknown EGGCC_SCOPED_MODE: {other}"),
        }
    }
}

/// Every projection follows its actual branch input; lexical roots remain
/// distinct and loop inputs stay opaque. No backedge equality is imported.
fn translate(expr: &RcExpr, expected: &Assumption, invariants: &[Invariant]) -> Option<Word> {
    if expr.get_ctx() != expected {
        return None;
    }
    match expr.as_ref() {
        Expr::Const(Constant::Int(k), _, _) => Some(Word::Constant(*k)),
        Expr::Arg(Type::Base(BaseType::IntT), ctx) => Some(Word::Slot(ctx.clone(), 0)),
        Expr::Get(arg, index) => {
            let Expr::Arg(Type::TupleT(fields), ctx) = arg.as_ref() else {
                return None;
            };
            if fields.get(*index) != Some(&BaseType::IntT) {
                return None;
            }
            if let Some(value) = constant_slot(ctx, *index, invariants) {
                Some(Word::Constant(value))
            } else if let Assumption::InIf(_, _, input) = ctx {
                translate(&project(input, *index)?, input.get_ctx(), invariants)
            } else {
                Some(Word::Slot(ctx.clone(), *index))
            }
        }
        Expr::Bop(op, a, b) => {
            let (a, b) = (
                Box::new(translate(a, expected, invariants)?),
                Box::new(translate(b, expected, invariants)?),
            );
            match op {
                BinaryOp::Add => Some(Word::Add(a, b)),
                BinaryOp::Mul => Some(Word::Mul(a, b)),
                BinaryOp::Bitand => Some(Word::Mask(a, b)),
                _ => None,
            }
        }
        _ => None,
    }
}

/// A true conjunction supplies only its actual comparison leaves. Boolean
/// projections may expand through their declared If input, never a sibling.
fn guard_leaves(expr: &RcExpr, expected: &Assumption) -> Option<Vec<RcExpr>> {
    if expr.get_ctx() != expected {
        return None;
    }
    match expr.as_ref() {
        Expr::Bop(BinaryOp::And, a, b) => {
            let mut leaves = guard_leaves(a, expected)?;
            leaves.extend(guard_leaves(b, expected)?);
            Some(leaves)
        }
        Expr::Get(arg, index) => {
            let Expr::Arg(Type::TupleT(fields), Assumption::InIf(_, _, input)) = arg.as_ref()
            else {
                return None;
            };
            if fields.get(*index) != Some(&BaseType::BoolT) {
                return None;
            }
            guard_leaves(&project(input, *index)?, input.get_ctx())
        }
        Expr::Bop(
            BinaryOp::GreaterEq | BinaryOp::LessThan | BinaryOp::LessEq | BinaryOp::GreaterThan,
            _,
            _,
        )
        | Expr::Const(Constant::Bool(_), _, _) => Some(vec![expr.clone()]),
        _ => None,
    }
}

fn initial_domain(expr: &RcExpr, expected: &Assumption, invariants: &[Invariant]) -> Option<Value> {
    let word = translate(expr, expected, invariants)?;
    match &word {
        Word::Constant(k) if (0..BASE).contains(k) => {
            return Some(json!({"kind":"literal","value":k}))
        }
        Word::Mask(_, mask) if matches!(mask.as_ref(), Word::Constant(k) if (0..=MASK).contains(k)) =>
        {
            let Word::Constant(value) = mask.as_ref() else {
                return None;
            };
            return Some(json!({"kind":"literal-mask","mask":value,"expression":expr.to_string()}));
        }
        _ => {}
    }
    let Expr::Get(arg, index) = expr.as_ref() else {
        return None;
    };
    let Expr::Arg(Type::TupleT(fields), Assumption::InIf(branch, predicate, input)) = arg.as_ref()
    else {
        return None;
    };
    if fields.get(*index) != Some(&BaseType::IntT) {
        return None;
    }
    if *branch {
        if let Some(leaves) = guard_leaves(predicate, predicate.get_ctx()) {
            let (mut low, mut high) = (None, None);
            for leaf in leaves {
                let Expr::Bop(op, a, b) = leaf.as_ref() else {
                    continue;
                };
                let (Some(a), Some(b)) = (
                    translate(a, leaf.get_ctx(), invariants),
                    translate(b, leaf.get_ctx(), invariants),
                ) else {
                    continue;
                };
                if *op == BinaryOp::GreaterEq && a == word && b == Word::Constant(0) {
                    low = Some(leaf.to_string());
                }
                if *op == BinaryOp::LessThan && a == word && b == Word::Constant(BASE) {
                    high = Some(leaf.to_string());
                }
            }
            if let (Some(low), Some(high)) = (low, high) {
                return Some(
                    json!({"kind":"true-conjunction-bounds","lower":low,"upper":high,"scope":expected.to_string()}),
                );
            }
        }
    }
    initial_domain(&project(input, *index)?, input.get_ctx(), invariants)
}

/// Only literals, already bounded slots, exact tuple/If transport and total
/// literal-mask operations can prove a backedge domain. Arithmetic alone cannot.
fn domain_scalar(
    expr: &RcExpr,
    expected: &Assumption,
    root: &Assumption,
    bounded: &BTreeSet<usize>,
    invariants: &[Invariant],
) -> Option<Value> {
    if expr.get_ctx() != expected {
        return None;
    }
    if let Some(word) = translate(expr, expected, invariants) {
        match word {
            Word::Constant(k) if (0..BASE).contains(&k) => {
                return Some(json!({"kind":"literal","value":k}))
            }
            Word::Slot(ctx, index) if ctx == *root && bounded.contains(&index) => {
                return Some(json!({"kind":"bounded-slot","slot":index}))
            }
            Word::Mask(_, mask) if matches!(mask.as_ref(), Word::Constant(k) if (0..=MASK).contains(k)) =>
            {
                let Word::Constant(value) = mask.as_ref() else {
                    return None;
                };
                return Some(
                    json!({"kind":"literal-mask","mask":value,"expression":expr.to_string()}),
                );
            }
            _ => {}
        }
    }
    let Expr::Get(tuple, index) = expr.as_ref() else {
        return None;
    };
    if let Expr::Arg(Type::TupleT(fields), Assumption::InIf(_, _, input)) = tuple.as_ref() {
        if fields.get(*index) != Some(&BaseType::IntT) {
            return None;
        }
        return domain_scalar(
            &project(input, *index)?,
            input.get_ctx(),
            root,
            bounded,
            invariants,
        );
    }
    domain_projection(tuple, *index, expected, root, bounded, invariants)
}

fn domain_projection(
    expr: &RcExpr,
    index: usize,
    expected: &Assumption,
    root: &Assumption,
    bounded: &BTreeSet<usize>,
    invariants: &[Invariant],
) -> Option<Value> {
    if expr.get_ctx() != expected {
        return None;
    }
    match expr.as_ref() {
        Expr::Single(value) if index == 0 => {
            domain_scalar(value, expected, root, bounded, invariants)
        }
        Expr::Concat(left, right) => {
            let length = tuple_length(left)?;
            if index < length {
                domain_projection(left, index, expected, root, bounded, invariants)
            } else {
                domain_projection(right, index - length, expected, root, bounded, invariants)
            }
        }
        Expr::Arg(Type::TupleT(fields), ctx) if fields.get(index) == Some(&BaseType::IntT) => {
            if ctx == root && bounded.contains(&index) {
                Some(json!({"kind":"bounded-slot","slot":index}))
            } else if let Assumption::InIf(_, _, input) = ctx {
                domain_scalar(
                    &project(input, index)?,
                    input.get_ctx(),
                    root,
                    bounded,
                    invariants,
                )
            } else {
                None
            }
        }
        Expr::If(pred, input, yes, no)
            if pred.get_ctx() == expected && input.get_ctx() == expected =>
        {
            let yes_ctx = Assumption::InIf(true, pred.clone(), input.clone());
            let no_ctx = Assumption::InIf(false, pred.clone(), input.clone());
            Some(
                json!({"kind":"both-branches","yes":domain_projection(yes,index,&yes_ctx,root,bounded,invariants)?,"no":domain_projection(no,index,&no_ctx,root,bounded,invariants)?}),
            )
        }
        _ => None,
    }
}

struct Domain {
    scope: Assumption,
    index: usize,
    certificate: Value,
}
fn loop_domains(program: &TreeProgram, invariants: &[Invariant]) -> Vec<Domain> {
    let mut stack = vec![program.entry.clone()];
    stack.extend(program.functions.clone());
    let (mut seen, mut domains) = (BTreeSet::new(), Vec::new());
    while let Some(expr) = stack.pop() {
        if !seen.insert(std::rc::Rc::as_ptr(&expr)) {
            continue;
        }
        stack.extend(expr.children_exprs());
        let Expr::DoWhile(initial, body) = expr.as_ref() else {
            continue;
        };
        let Type::TupleT(fields) = body.get_arg_type() else {
            continue;
        };
        let root = body.get_ctx();
        let initial_proofs = fields
            .iter()
            .enumerate()
            .filter_map(|(index, ty)| {
                if *ty != BaseType::IntT {
                    return None;
                }
                let value = project(initial, index)?;
                Some((
                    index,
                    initial_domain(&value, initial.get_ctx(), invariants)?,
                ))
            })
            .collect::<Vec<_>>();
        let mut bounded = initial_proofs
            .iter()
            .map(|(i, _)| *i)
            .collect::<BTreeSet<_>>();
        loop {
            let retained = bounded
                .iter()
                .copied()
                .filter(|index| {
                    domain_projection(body, index + 1, root, root, &bounded, invariants).is_some()
                })
                .collect::<BTreeSet<_>>();
            if retained == bounded {
                break;
            }
            bounded = retained;
        }
        for (index, initial_proof) in initial_proofs {
            if !bounded.contains(&index) {
                continue;
            }
            let Some(backedge) =
                domain_projection(body, index + 1, root, root, &bounded, invariants)
            else {
                continue;
            };
            domains.push(Domain { scope:root.clone(), index, certificate:json!({"input_slot":index,"output_slot":index+1,"scope":root.to_string(),"initial":initial_proof,"backedge":backedge}) });
        }
    }
    domains
}

fn unpack(word: &Word) -> Option<(&Word, &Word)> {
    let Word::Add(high, low) = word else {
        return None;
    };
    let Word::Mul(field, base) = high.as_ref() else {
        return None;
    };
    if base.as_ref() != &Word::Constant(BASE) {
        return None;
    }
    Some((field, low))
}

fn collect_masks(value: &Value, masks: &mut Vec<i64>) {
    match value {
        Value::Object(fields) => {
            if let Some(mask) = fields.get("mask").and_then(Value::as_i64) {
                masks.push(mask);
            }
            for child in fields.values() {
                collect_masks(child, masks);
            }
        }
        Value::Array(children) => {
            for child in children {
                collect_masks(child, masks);
            }
        }
        _ => {}
    }
}

/// Independent least fixed point on exactly the same finite applications and
/// original seeds. It owns congruence, cancellation and both disequality edges.
fn manual(
    cancellation: bool,
    reverse: bool,
    forward: bool,
    equality_rescue: bool,
    disequality_rescue: bool,
) -> ([bool; 5], bool) {
    let rows = [
        ("ThisScope", vec![], 9, false),
        ("A", vec![9], 0, false),
        ("B", vec![9], 1, false),
        ("C", vec![9], 2, false),
        ("D", vec![9], 3, false),
        ("Pack32", vec![0, 1], 4, cancellation),
        ("Pack32", vec![2, 3], 5, cancellation),
        ("Pack32", vec![2, 0], 6, cancellation),
        ("Shift7", vec![2], 7, forward),
        ("Shift7", vec![3], 8, forward),
    ];
    let mut equality = (0..10).collect::<Vec<_>>();
    equality[5] = 4;
    if equality_rescue {
        equality[2] = 0;
    }
    let mut unequal = BTreeSet::from([(4, 6)]);
    if disequality_rescue {
        unequal.insert((2, 3));
    }
    loop {
        let before = (equality.clone(), unequal.clone());
        for (name, children, output, marked) in &rows {
            for (other, other_children, other_output, _) in &rows {
                if name != other {
                    continue;
                }
                if children
                    .iter()
                    .zip(other_children)
                    .all(|(a, b)| equality[*a] == equality[*b])
                {
                    let (old, new) = (equality[*other_output], equality[*output]);
                    for item in &mut equality {
                        if *item == old {
                            *item = new;
                        }
                    }
                }
                if *marked && equality[*output] == equality[*other_output] {
                    for (a, b) in children.iter().zip(other_children) {
                        let (old, new) = (equality[*b], equality[*a]);
                        for item in &mut equality {
                            if *item == old {
                                *item = new;
                            }
                        }
                    }
                }
            }
        }
        unequal = unequal
            .into_iter()
            .map(|(a, b)| {
                let (a, b) = (equality[a], equality[b]);
                (a.min(b), a.max(b))
            })
            .collect();
        for (name, children, output, marked) in &rows {
            for (other, other_children, other_output, _) in &rows {
                if name != other {
                    continue;
                }
                let (a, b) = (equality[*output], equality[*other_output]);
                let parent = (a.min(b), a.max(b));
                for (index, (a, b)) in children.iter().zip(other_children).enumerate() {
                    let (a, b) = (equality[*a], equality[*b]);
                    let child = (a.min(b), a.max(b));
                    if *marked && unequal.contains(&child) {
                        unequal.insert(parent);
                    }
                    if reverse
                        && unequal.contains(&parent)
                        && children
                            .iter()
                            .zip(other_children)
                            .enumerate()
                            .all(|(i, (a, b))| i == index || equality[*a] == equality[*b])
                    {
                        unequal.insert(child);
                    }
                }
            }
        }
        if before == (equality.clone(), unequal.clone()) {
            break;
        }
    }
    let known = [(0, 1), (2, 3), (7, 8)].map(|(a, b)| {
        let (a, b) = (equality[a], equality[b]);
        unequal.contains(&(a.min(b), a.max(b)))
    });
    (
        [
            equality[0] == equality[2],
            equality[1] == equality[3],
            known[0],
            known[1],
            known[2],
        ],
        unequal.iter().any(|(a, b)| a == b),
    )
}

fn disequality_query(
    graph: &mut egglog::EGraph,
    name: &str,
    a: &str,
    b: &str,
    reverse: bool,
) -> Result<bool, Error> {
    graph.parse_and_run_program(None,&format!("(relation {name} ())\n(ruleset {name}-query)\n(rule (({} {a} {b})) (({name})) :ruleset {name}-query :naive)\n(run-schedule (run {name}-query))",if reverse {"known-disequal?"} else {"known-disequal-forward-only?"}))?;
    Ok(graph.get_size(name) > 0)
}

fn equality_query(graph: &mut egglog::EGraph, a: &str, b: &str) -> Result<bool, Error> {
    match graph.parse_and_run_program(None, &format!("(check (= {a} {b}))")) {
        Ok(_) => Ok(true),
        Err(Error::CheckError(..)) => Ok(false),
        Err(error) => Err(error),
    }
}

fn prove(mode: Mode) -> Result<(bool, Value), Error> {
    let cancellation = !matches!(mode, Mode::CancellationOff | Mode::CancellationRescue);
    let reverse = !matches!(mode, Mode::ReverseOff | Mode::DisequalityRescue);
    let forward = mode != Mode::ForwardOff;
    let equality_rescue = mode == Mode::CancellationRescue;
    let disequality_rescue = mode == Mode::DisequalityRescue;
    let inference = !matches!(mode, Mode::SeedOnly | Mode::PrimitiveOnly);
    let mut program=format!("(datatype Scope (ThisScope))\n(datatype Field32)\n(datatype Word)\n(constructor A (Scope) Field32)\n(constructor B (Scope) Field32)\n(constructor C (Scope) Field32)\n(constructor D (Scope) Field32)\n(constructor Pack32 (Field32 Field32) Word {})\n(constructor Shift7 (Field32) Word {})\n(let pk32-a (A (ThisScope)))\n(let pk32-b (B (ThisScope)))\n(let pk32-c (C (ThisScope)))\n(let pk32-d (D (ThisScope)))\n(let pk32-ab (Pack32 pk32-a pk32-b))\n(let pk32-cd (Pack32 pk32-c pk32-d))\n(let pk32-ca (Pack32 pk32-c pk32-a))\n(let pk32-tc (Shift7 pk32-c))\n(let pk32-td (Shift7 pk32-d))\n(union pk32-ab pk32-cd)\n(disequal pk32-ca pk32-ab)\n",if cancellation {":injective"} else {""},if forward {":injective"} else {""});
    let original_graph_and_seeds = program.clone();
    if equality_rescue {
        program.push_str("(union pk32-a pk32-c)\n");
    }
    if disequality_rescue {
        program.push_str("(disequal pk32-c pk32-d)\n");
    }
    if inference && mode != Mode::Manual {
        program.push_str("(run-schedule (saturate injectivity))\n");
    }
    let mut graph = new_experimental_egraph_with_options(false, DisequalityEncoding::Nee);
    graph.parse_and_run_program(None, &program)?;
    let (mut known, mut bottom) = ([false; 5], false);
    if mode == Mode::Manual {
        (known, bottom) = manual(
            cancellation,
            reverse,
            forward,
            equality_rescue,
            disequality_rescue,
        );
    } else if inference {
        bottom = match graph.parse_and_run_program(None, "(check-contradiction)") {
            Ok(_) => true,
            Err(Error::CheckError(..)) => false,
            Err(error) => return Err(error),
        };
        if !bottom {
            known[0] = equality_query(&mut graph, "pk32-a", "pk32-c")?;
            known[1] = equality_query(&mut graph, "pk32-b", "pk32-d")?;
            for (index, name, a, b) in [
                (2, "ABKnown", "pk32-a", "pk32-b"),
                (3, "CDKnown", "pk32-c", "pk32-d"),
                (4, "TargetKnown", "pk32-tc", "pk32-td"),
            ] {
                if index == 4 && mode == Mode::QueryOff {
                    continue;
                }
                known[index] = disequality_query(&mut graph, name, a, b, reverse)?;
            }
        }
    }
    let export = inference && !bottom && known[4] && mode != Mode::BridgeOff;
    Ok((
        export,
        json!({"program":program,"original_graph_and_seeds":original_graph_and_seeds,
        "mode":format!("{mode:?}"),"encoding":"NEE","a_eq_c":if inference {Some(known[0])} else {None},"b_eq_d":if inference {Some(known[1])} else {None},
        "a_neq_b":if inference {Some(known[2])} else {None},"c_neq_d":if inference {Some(known[3])} else {None},"target_neq":if inference && mode!=Mode::QueryOff {Some(known[4])} else {None},
        "bottom":if inference {Some(bottom)} else {None},"bottom_checked":inference,"export":export,"consumer_enabled":mode!=Mode::ConsumerOff,
        "pack32_marked":cancellation,"shift7_marked":forward,"reverse_enabled":reverse,"equality_rescue":equality_rescue,"disequality_rescue":disequality_rescue,
        "original_equality_seed":true,"original_disequality_seed":true,"injectivity_saturated":inference && mode!=Mode::Manual,"engine_witness_queries_run":inference && mode!=Mode::Manual,
        "manual_closure_run":mode==Mode::Manual,"equality_sort_reasoning_enabled":inference,"primitive_only_marked_fields":[],"primitive_only_witness":false}),
    ))
}

/// Recognize only the two exact path predicates and the fixed translated
/// target; each Field32 leaf requires its own loop domain certificate.
pub(crate) fn analyze(program: &TreeProgram) -> Vec<RcExpr> {
    let mode = Mode::from_env();
    if mode == Mode::Off {
        return Vec::new();
    }
    static BOUNDARY: AtomicUsize = AtomicUsize::new(0);
    let boundary = BOUNDARY.fetch_add(1, Ordering::Relaxed);
    let types = program.typecheck();
    let invariants = loop_invariants(program);
    let domains = loop_domains(program, &invariants);
    let mut stack = vec![program.entry.clone()];
    stack.extend(program.functions.clone());
    let (mut seen, mut exports, mut receipts) = (BTreeSet::new(), Vec::new(), Vec::new());
    while let Some(expr) = stack.pop() {
        if !seen.insert(std::rc::Rc::as_ptr(&expr)) {
            continue;
        }
        stack.extend(expr.children_exprs());
        let Expr::If(target, _, _, _) = expr.as_ref() else {
            continue;
        };
        let Expr::Bop(BinaryOp::Eq, tc, td) = target.as_ref() else {
            continue;
        };
        if types.get(&std::rc::Rc::as_ptr(target)) != Some(&Type::Base(BaseType::BoolT)) {
            continue;
        }
        let target_scope = target.get_ctx();
        let Assumption::InIf(false, second, second_input) = target_scope else {
            continue;
        };
        let Expr::Bop(BinaryOp::Eq, sa, sb) = second.as_ref() else {
            continue;
        };
        let second_scope = second.get_ctx();
        let Assumption::InIf(true, first, first_input) = second_scope else {
            continue;
        };
        let Expr::Bop(BinaryOp::Eq, fa, fb) = first.as_ref() else {
            continue;
        };
        let root = first.get_ctx();
        let words = (
            translate(fa, root, &invariants),
            translate(fb, root, &invariants),
            translate(sa, second_scope, &invariants),
            translate(sb, second_scope, &invariants),
            translate(tc, target_scope, &invariants),
            translate(td, target_scope, &invariants),
        );
        let mut accepted = None;
        if let (Some(fa), Some(fb), Some(sa), Some(sb), Some(tc), Some(td)) = &words {
            for (left, right) in [(fa, fb), (fb, fa)] {
                let (Some((a, b)), Some((c, d))) = (unpack(left), unpack(right)) else {
                    continue;
                };
                let second_expected = Word::Add(
                    Box::new(Word::Mul(
                        Box::new(c.clone()),
                        Box::new(Word::Constant(BASE)),
                    )),
                    Box::new(a.clone()),
                );
                let second_matches = (sa == &second_expected && sb == left)
                    || (sb == &second_expected && sa == left);
                let targets = (
                    Word::Add(Box::new(c.clone()), Box::new(Word::Constant(7))),
                    Word::Add(Box::new(d.clone()), Box::new(Word::Constant(7))),
                );
                if !second_matches
                    || !((tc == &targets.0 && td == &targets.1)
                        || (td == &targets.0 && tc == &targets.1))
                {
                    continue;
                }
                let Word::Slot(field_root, _) = a else {
                    continue;
                };
                let certificates = [a, b, c, d]
                    .iter()
                    .map(|word| {
                        let Word::Slot(scope, index) = word else {
                            return None;
                        };
                        if scope != field_root {
                            return None;
                        }
                        domains
                            .iter()
                            .find(|domain| domain.scope == *scope && domain.index == *index)
                            .map(|domain| domain.certificate.clone())
                    })
                    .collect::<Option<Vec<_>>>();
                if let Some(certificates) = certificates {
                    accepted = Some((format!("{a:?},{b:?},{c:?},{d:?}"), certificates));
                    break;
                }
            }
        }
        let Some((fields, certificates)) = accepted else {
            receipts.push(json!({"accepted":false,"export":false,"reason":"exact packing, transport, target or bounded-domain mismatch","source_target":target.to_string(),"source_first":first.to_string(),"source_second":second.to_string(),"translated":format!("{words:?}"),"domain_count":domains.len(),"domains":domains.iter().map(|domain| json!({"scope":domain.scope.to_string(),"index":domain.index,"certificate":domain.certificate})).collect::<Vec<_>>()}));
            continue;
        };
        let (export, mut receipt) = match prove(mode) {
            Ok(value) => value,
            Err(error) => (
                false,
                json!({"analysis_error":format!("{error:?}"),"export":false}),
            ),
        };
        let mut masks = Vec::new();
        for certificate in &certificates {
            collect_masks(certificate, &mut masks);
        }
        let comparisons = if mode == Mode::PrimitiveOnly {
            let mut comparisons = Vec::new();
            for (name, values) in [
                ("pack_base", vec![BASE; 3]),
                ("target_shift", vec![7; 2]),
                ("backedge_mask", masks.clone()),
                ("field_lower_bound", vec![0; 4]),
                ("field_upper_bound", vec![BASE; 4]),
            ] {
                for (index, a) in values.iter().enumerate() {
                    for b in values.iter().skip(index + 1) {
                        comparisons.push(json!({"field":name,"left":a,"right":b,"equal":a==b}));
                    }
                }
            }
            comparisons
        } else {
            Vec::new()
        };
        receipt["accepted"] = json!(true);
        receipt["source_signature"] = json!({"target":target.to_string(),"first":first.to_string(),"second":second.to_string(),"first_input":first_input.to_string(),"second_input":second_input.to_string(),"fields":fields,"domains":certificates});
        receipt["primitive_comparisons"] = json!(comparisons);
        receipt["source_metadata"] = json!({"pack_bases":vec![BASE;3],"target_shifts":vec![7;2],"lower_bound":0,"upper_bound":BASE,"backedge_masks":masks,"mask_ceiling":MASK});
        receipts.push(receipt);
        if export {
            exports.push(target.clone());
        }
    }
    if let Ok(directory) = std::env::var("EGGCC_SCOPED_EVIDENCE") {
        std::fs::create_dir_all(&directory).unwrap();
        let path = Path::new(&directory).join(format!("boundary-{boundary:04}.json"));
        assert!(!path.exists());
        std::fs::write(path,serde_json::to_vec_pretty(&json!({"boundary":boundary,"mode":format!("{mode:?}"),"queries":receipts,"exports":exports.len()})).unwrap()).unwrap();
    }
    exports
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn pack32_generic_chain_and_true_intermediate_rescues() {
        for mode in [
            Mode::SeedOnly,
            Mode::PrimitiveOnly,
            Mode::CancellationOff,
            Mode::CancellationRescue,
            Mode::ReverseOff,
            Mode::DisequalityRescue,
            Mode::ForwardOff,
            Mode::QueryOff,
            Mode::Manual,
            Mode::Encoding,
            Mode::BridgeOff,
            Mode::ConsumerOff,
        ] {
            let (export, receipt) = prove(mode).unwrap();
            assert_eq!(
                export,
                matches!(
                    mode,
                    Mode::Encoding
                        | Mode::Manual
                        | Mode::CancellationRescue
                        | Mode::DisequalityRescue
                        | Mode::ConsumerOff
                ),
                "{receipt}"
            );
            if matches!(
                mode,
                Mode::Encoding
                    | Mode::Manual
                    | Mode::DisequalityRescue
                    | Mode::ForwardOff
                    | Mode::ReverseOff
            ) {
                assert_eq!(receipt["a_eq_c"], true, "{receipt}");
                assert_eq!(receipt["b_eq_d"], true, "{receipt}");
            }
            if mode == Mode::CancellationRescue {
                assert_eq!(receipt["a_eq_c"], true, "{receipt}");
                assert_eq!(receipt["b_eq_d"], false, "{receipt}");
                assert_eq!(receipt["c_neq_d"], true, "{receipt}");
            }
            if mode == Mode::CancellationOff {
                assert_eq!(receipt["a_eq_c"], false);
                assert_eq!(receipt["b_eq_d"], false);
            }
            if mode == Mode::ReverseOff {
                assert_eq!(receipt["c_neq_d"], false);
            }
            if mode == Mode::ForwardOff {
                assert_eq!(receipt["c_neq_d"], true);
                assert_eq!(receipt["target_neq"], false);
            }
            if matches!(mode, Mode::SeedOnly | Mode::PrimitiveOnly) {
                assert_eq!(receipt["original_equality_seed"], true);
                assert_eq!(receipt["original_disequality_seed"], true);
                assert_eq!(receipt["bottom_checked"], false);
                assert_eq!(receipt["manual_closure_run"], false);
                assert_eq!(receipt["engine_witness_queries_run"], false);
                assert!(!receipt["program"]
                    .as_str()
                    .unwrap()
                    .contains("run-schedule"));
            }
        }
    }

    #[test]
    fn pack32_manual_closure_needs_all_three_edges() {
        assert_eq!(manual(true, true, true, false, false).0, [true; 5]);
        assert_eq!(manual(false, true, true, false, false).0, [false; 5]);
        assert_eq!(
            manual(true, false, true, false, false).0,
            [true, true, false, false, false]
        );
        assert_eq!(
            manual(true, true, false, false, false).0,
            [true, true, true, true, false]
        );
        assert_eq!(
            manual(false, true, true, true, false).0,
            [true, false, true, true, true]
        );
        assert_eq!(manual(true, false, true, false, true).0, [true; 5]);
    }

    #[test]
    fn pack32_missing_seeds_and_two_unresolved_children_remain_unknown() {
        let (_, receipt) = prove(Mode::SeedOnly).unwrap();
        let original = receipt["program"].as_str().unwrap();
        for removed in ["(union pk32-ab pk32-cd)\n", "(disequal pk32-ca pk32-ab)\n"] {
            let mut graph = new_experimental_egraph_with_options(false, DisequalityEncoding::Nee);
            let program = original.replace(removed, "") + "(run-schedule (saturate injectivity))\n";
            graph.parse_and_run_program(None, &program).unwrap();
            assert!(
                !disequality_query(&mut graph, "NoTarget", "pk32-tc", "pk32-td", true).unwrap()
            );
            if removed.starts_with("(union") {
                assert!(!disequality_query(
                    &mut graph,
                    "NoUnresolvedChild",
                    "pk32-a",
                    "pk32-b",
                    true
                )
                .unwrap());
            }
        }
    }

    #[test]
    fn pack32_domain_boundary_collisions_forbid_unrestricted_marking() {
        let pack = |a: i64, b: i64| a.wrapping_mul(BASE).wrapping_add(b);
        assert_eq!(pack(BASE, 0), pack(0, 0));
        assert_eq!(pack(0, BASE), pack(1, 0));
        assert_eq!(pack(-1, MASK), pack(MASK, MASK));
        assert_ne!(pack(0, 0), pack(0, 1));
        assert_ne!(pack(0, 0), pack(1, 0));
    }

    fn integer_slot(scope: &Assumption, index: usize) -> RcExpr {
        RcExpr::new(Expr::Get(
            RcExpr::new(Expr::Arg(
                Type::TupleT(vec![BaseType::IntT; 2]),
                scope.clone(),
            )),
            index,
        ))
    }

    #[test]
    fn pack32_transport_rejects_sibling_and_wrong_types() {
        use crate::ast::*;
        use crate::{parallel, tuplet};
        let root = Assumption::InFunc("parent".to_owned());
        let input = parallel!(int(7), int(8))
            .with_arg_types(base(intt()), tuplet!(intt(), intt()))
            .add_ctx(root.clone())
            .0;
        let predicate = eq(int(0), int(1))
            .with_arg_types(base(intt()), base(boolt()))
            .add_ctx(root)
            .0;
        let yes = Assumption::InIf(true, predicate.clone(), input.clone());
        let no = Assumption::InIf(false, predicate, input);
        let value = integer_slot(&yes, 0);
        assert_eq!(translate(&value, &yes, &[]), Some(Word::Constant(7)));
        assert_eq!(translate(&value, &no, &[]), None);
        let bad = RcExpr::new(Expr::Get(
            RcExpr::new(Expr::Arg(Type::TupleT(vec![BaseType::BoolT]), yes.clone())),
            0,
        ));
        assert_eq!(translate(&bad, &yes, &[]), None);
    }

    #[test]
    fn pack32_domain_needs_guarded_initial_and_every_backedge() {
        use crate::ast::*;
        use crate::{parallel, tuplet};
        for (initial, body, expected) in [
            (
                parallel!(int(1), int(MASK)),
                parallel!(tfalse(), bitand(add(getat(0), int(1)), getat(1)), getat(1)),
                true,
            ),
            (
                parallel!(int(BASE), int(MASK)),
                parallel!(tfalse(), bitand(add(getat(0), int(1)), getat(1)), getat(1)),
                false,
            ),
            (
                parallel!(int(1), int(MASK)),
                parallel!(tfalse(), add(getat(0), int(1)), getat(1)),
                false,
            ),
            (
                parallel!(int(1), int(MASK)),
                parallel!(
                    tfalse(),
                    bitand(add(getat(0), int(1)), getat(1)),
                    add(getat(1), int(1))
                ),
                false,
            ),
        ] {
            let function = function(
                "main",
                base(intt()),
                tuplet!(intt(), intt()),
                dowhile(initial, body),
            )
            .func_with_arg_types()
            .func_add_ctx()
            .0;
            let program = function.func_to_program();
            let invariants = loop_invariants(&program);
            let domains = loop_domains(&program, &invariants);
            assert_eq!(domains.iter().any(|domain| domain.index == 0), expected);
        }
    }

    #[test]
    fn pack32_true_guard_proves_both_bounds_only() {
        let root = Assumption::InFunc("bounds".to_owned());
        let field = integer_slot(&root, 0);
        let constant = |value| {
            RcExpr::new(Expr::Const(
                Constant::Int(value),
                Type::TupleT(vec![BaseType::IntT; 2]),
                root.clone(),
            ))
        };
        let low = RcExpr::new(Expr::Bop(BinaryOp::GreaterEq, field.clone(), constant(0)));
        let high = RcExpr::new(Expr::Bop(BinaryOp::LessThan, field.clone(), constant(BASE)));
        let both = RcExpr::new(Expr::Bop(BinaryOp::And, low.clone(), high));
        let input = RcExpr::new(Expr::Arg(Type::TupleT(vec![BaseType::IntT; 2]), root));
        for (branch, predicate, expected) in [
            (true, both.clone(), true),
            (false, both, false),
            (true, low, false),
        ] {
            let scope = Assumption::InIf(branch, predicate, input.clone());
            assert_eq!(
                initial_domain(&integer_slot(&scope, 0), &scope, &[]).is_some(),
                expected
            );
        }
    }

    #[test]
    fn pack32_ee_nee_consistent_graph_differential() {
        for mode in [
            Mode::Encoding,
            Mode::CancellationOff,
            Mode::CancellationRescue,
            Mode::ReverseOff,
            Mode::DisequalityRescue,
            Mode::ForwardOff,
        ] {
            let (_, receipt) = prove(mode).unwrap();
            let mut graph = new_experimental_egraph_with_options(false, DisequalityEncoding::Ee);
            graph
                .parse_and_run_program(None, receipt["program"].as_str().unwrap())
                .unwrap();
            assert!(matches!(
                graph.parse_and_run_program(None, "(check-contradiction)"),
                Err(Error::CheckError(..))
            ));
            for (a, b, key) in [
                ("pk32-a", "pk32-c", "a_eq_c"),
                ("pk32-b", "pk32-d", "b_eq_d"),
            ] {
                assert_eq!(
                    json!(equality_query(&mut graph, a, b).unwrap()),
                    receipt[key]
                );
            }
            for (name, a, b, key) in [
                ("EEAB", "pk32-a", "pk32-b", "a_neq_b"),
                ("EECD", "pk32-c", "pk32-d", "c_neq_d"),
                ("EETarget", "pk32-tc", "pk32-td", "target_neq"),
            ] {
                assert_eq!(
                    json!(disequality_query(
                        &mut graph,
                        name,
                        a,
                        b,
                        !matches!(mode, Mode::ReverseOff | Mode::DisequalityRescue)
                    )
                    .unwrap()),
                    receipt[key]
                );
            }
        }
    }
}
