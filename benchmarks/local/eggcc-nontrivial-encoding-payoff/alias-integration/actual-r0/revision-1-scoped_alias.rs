//! Exact-profile A1 experiment. No path assumption or unscoped NoAlias row is
//! exported. One checked demand enables one commute, then its token is retired.
use egglog::{new_experimental_egraph_with_options, DisequalityEncoding, EGraph, Error, Write};
use serde::Deserialize;
use serde_json::{json, Value as Json};
use std::{
    collections::{BTreeMap, BTreeSet, VecDeque},
    path::Path,
};

#[derive(Clone, Debug, Deserialize)]
struct Node {
    op: String,
    children: Vec<String>,
    eclass: String,
}

/// Only constructor rows establish expression ancestry. Context and analysis
/// edges are deliberately absent; Arg/Const/Empty are lexical leaves.
struct Graph {
    nodes: BTreeMap<String, Node>,
    classes: BTreeMap<String, Vec<String>>,
    gets: BTreeMap<(String, usize), BTreeSet<String>>,
}

impl Graph {
    fn read(egraph: &EGraph) -> Result<Self, Error> {
        let serialized = serde_json::to_value(egraph.serialize(Default::default()).egraph)
            .map_err(|e| Error::BackendError(e.to_string()))?;
        Self::from_json(serialized).map_err(Error::BackendError)
    }

    fn from_json(serialized: Json) -> Result<Self, String> {
        let nodes: BTreeMap<String, Node> =
            serde_json::from_value(serialized["nodes"].clone()).map_err(|e| e.to_string())?;
        let mut graph = Self {
            nodes,
            classes: BTreeMap::new(),
            gets: BTreeMap::new(),
        };
        for (key, node) in &graph.nodes {
            graph
                .classes
                .entry(node.eclass.clone())
                .or_default()
                .push(key.clone());
        }
        for node in graph.nodes.values().filter(|n| n.op == "Get") {
            if let [source, index] = node.children.as_slice() {
                if let Some(index) = graph
                    .primitive_int(&graph.nodes[index].eclass)
                    .and_then(|x| usize::try_from(x).ok())
                {
                    graph
                        .gets
                        .entry((graph.nodes[source].eclass.clone(), index))
                        .or_default()
                        .insert(node.eclass.clone());
                }
            }
        }
        Ok(graph)
    }

    /// Reject competing constructor representations instead of selecting the
    /// first convenient row. Multiple identical canonical child lists are fine.
    fn unique(&self, class: &str, op: &str) -> Option<Vec<String>> {
        let alternatives: BTreeSet<Vec<String>> = self
            .classes
            .get(class)?
            .iter()
            .map(|k| &self.nodes[k])
            .filter(|n| n.op == op)
            .map(|n| {
                n.children
                    .iter()
                    .map(|c| self.nodes[c].eclass.clone())
                    .collect()
            })
            .collect();
        (alternatives.len() == 1).then(|| alternatives.into_iter().next().unwrap())
    }

    fn primitive_int(&self, class: &str) -> Option<i64> {
        let alternatives: BTreeSet<i64> = self
            .classes
            .get(class)?
            .iter()
            .map(|k| &self.nodes[k])
            .filter(|n| n.children.is_empty())
            .filter_map(|n| n.op.parse().ok())
            .collect();
        (alternatives.len() == 1).then(|| *alternatives.iter().next().unwrap())
    }

    fn literal(&self, class: &str) -> Option<i64> {
        let constant = self.unique(class, "Const")?;
        let value = self.unique(constant.first()?, "Int")?;
        self.primitive_int(value.first()?)
    }

    fn tagged(&self, class: &str, name: &str) -> bool {
        self.classes
            .get(class)
            .is_some_and(|keys| keys.iter().any(|k| self.nodes[k].op == name))
    }

    fn operator(&self, class: &str, constructor: &str, tag: &str) -> Option<Vec<String>> {
        let alternatives: BTreeSet<Vec<String>> = self
            .classes
            .get(class)?
            .iter()
            .map(|k| &self.nodes[k])
            .filter(|n| {
                n.op == constructor
                    && n.children
                        .first()
                        .is_some_and(|c| self.tagged(&self.nodes[c].eclass, tag))
            })
            .map(|n| {
                let mut children = n
                    .children
                    .iter()
                    .skip(1)
                    .map(|c| self.nodes[c].eclass.clone())
                    .collect::<Vec<_>>();
                // The normal U0 graph contains both orientations of these
                // commutative operators. Normalize only those proved laws.
                if children.len() == 2 && matches!(tag, "Eq" | "And" | "Add" | "Bitand") {
                    let left_literal = self.literal(&children[0]).is_some();
                    let right_literal = self.literal(&children[1]).is_some();
                    if (matches!(tag, "Add" | "Bitand") && left_literal && !right_literal)
                        || ((left_literal == right_literal || matches!(tag, "Eq" | "And"))
                            && children[1] < children[0])
                    {
                        children.swap(0, 1);
                    }
                }
                children
            })
            .collect();
        (alternatives.len() == 1).then(|| alternatives.into_iter().next().unwrap())
    }

    fn relation_value(&self, relation: &str, expr: &str) -> Option<String> {
        let values: BTreeSet<String> = self
            .nodes
            .values()
            .filter(|n| {
                n.op == relation
                    && n.children.len() == 2
                    && self.nodes[&n.children[0]].eclass == expr
            })
            .map(|n| self.nodes[&n.children[1]].eclass.clone())
            .collect();
        (values.len() == 1).then(|| values.into_iter().next().unwrap())
    }

    fn scalar_type(&self, expr: &str, base: &str) -> bool {
        self.relation_value("HasType", expr)
            .and_then(|t| self.unique(&t, "Base"))
            .is_some_and(|x| x.len() == 1 && self.tagged(&x[0], base))
    }

    fn int_pointer(&self, expr: &str) -> bool {
        self.relation_value("HasType", expr)
            .and_then(|t| self.unique(&t, "Base"))
            .and_then(|b| self.unique(&b[0], "PointerT"))
            .is_some_and(|x| x.len() == 1 && self.tagged(&x[0], "IntT"))
    }

    fn project(&self, tuple: &str, index: usize) -> Option<String> {
        let values = self.gets.get(&(tuple.to_owned(), index))?;
        (values.len() == 1).then(|| values.iter().next().unwrap().clone())
    }

    /// Return a unique actual typed Arg projection in precisely this context.
    fn binding(&self, expr: &str, context: &str) -> Option<(String, usize)> {
        let mut values = BTreeSet::new();
        for key in self.classes.get(expr)? {
            let node = &self.nodes[key];
            if node.op != "Get" || node.children.len() != 2 {
                continue;
            }
            let source = &self.nodes[&node.children[0]].eclass;
            let Some(arg) = self.unique(source, "Arg") else {
                continue;
            };
            if arg.get(1).map(String::as_str) != Some(context) {
                continue;
            }
            let Some(index) = self
                .primitive_int(&self.nodes[&node.children[1]].eclass)
                .and_then(|i| usize::try_from(i).ok())
            else {
                continue;
            };
            if self.project(source, index).as_deref() == Some(expr) {
                values.insert((source.clone(), index));
            }
        }
        (values.len() == 1).then(|| values.into_iter().next().unwrap())
    }

    fn reachable(&self, start: &str, target: &str) -> bool {
        let mut queue = VecDeque::from([start.to_owned()]);
        let mut seen = BTreeSet::new();
        while let Some(class) = queue.pop_front() {
            if class == target {
                return true;
            }
            if !seen.insert(class.clone()) {
                continue;
            }
            let Some(keys) = self.classes.get(&class) else {
                continue;
            };
            for key in keys {
                let n = &self.nodes[key];
                let positions: &[usize] = match n.op.as_str() {
                    "Get" | "SubTuple" | "Single" | "Uop" => &[0],
                    "Concat" | "DoWhile" => &[0, 1],
                    "Bop" => &[1, 2],
                    "Top" => &[1, 2, 3],
                    "Alloc" => &[1, 2],
                    "If" => &[0, 1, 2, 3],
                    "Function" => &[3],
                    _ => &[],
                };
                for &index in positions {
                    if let Some(child) = n.children.get(index) {
                        queue.push_back(self.nodes[child].eclass.clone())
                    }
                }
            }
        }
        false
    }

    /// Localize only through actual enclosing If inputs, ending at one common
    /// function's integer slot. A loop Arg is never treated as a fresh root.
    fn tuple_signature(&self, ty: &str) -> Option<Vec<String>> {
        let mut list = self.unique(ty, "TupleT")?.first()?.clone();
        let mut types = Vec::new();
        for _ in 0..16 {
            if self.tagged(&list, "TNil") { return Some(types); }
            let row = self.unique(&list, "TCons")?;
            let names = ["IntT", "StateT"].into_iter().filter(|name| self.tagged(&row[0], name)).collect::<Vec<_>>();
            if names.len() != 1 { return None; }
            types.push(names[0].to_owned()); list = row[1].clone();
        }
        None
    }

    fn word(&self, expr: &str, expected: &str, depth: usize) -> Option<Word> {
        if depth > 32
            || !self.scalar_type(expr, "IntT")
            || self.relation_value("ContextOf", expr)?.as_str() != expected
        {
            return None;
        }
        if let Some(value) = self.literal(expr) {
            return Some(Word::Literal(value));
        }
        let (_, index) = self.binding(expr, expected)?;
        if self.unique(expected, "InLoop").is_some() {
            return None;
        }
        if let Some(function) = self.unique(expected, "InFunc") {
            if self.unique(expected, "InIf").is_some() { return None; }
            let roots = self.nodes.values().filter(|n| n.op == "Function").collect::<Vec<_>>();
            if roots.len() != 1 || self.nodes[&roots[0].children[0]].eclass != function[0] { return None; }
            return Some(Word::Slot(expected.to_owned(), index));
        }
        let branch = self.unique(expected, "InIf")?;
        let input = self.project(&branch[2], index)?;
        self.word(
            &input,
            &self.relation_value("ContextOf", &branch[2])?,
            depth + 1,
        )
    }

    fn true_guards(
        &self,
        pred: &str,
        context: &str,
        depth: usize,
    ) -> Option<Vec<(String, Word, Word)>> {
        if depth > 16
            || !self.scalar_type(pred, "BoolT")
            || self.relation_value("ContextOf", pred)?.as_str() != context
        {
            return None;
        }
        if let Some(and) = self.operator(pred, "Bop", "And") {
            let mut left = self.true_guards(&and[0], context, depth + 1)?;
            left.extend(self.true_guards(&and[1], context, depth + 1)?);
            return Some(left);
        }
        for op in ["GreaterEq", "LessThan", "LessEq"] {
            if let Some(children) = self.operator(pred, "Bop", op) {
                return Some(vec![(
                    op.to_owned(),
                    self.word(&children[0], context, 0)?,
                    self.word(&children[1], context, 0)?,
                )]);
            }
        }
        None
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Word {
    Slot(String, usize),
    Literal(i64),
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct Certificate {
    branch: String,
    loop_context: String,
    target_context: String,
    loop_expr: String,
    allocation: String,
    base: String,
    local_i: String,
    local_j: String,
    branch_pi: String,
    branch_pj: String,
    loop_pi: String,
    loop_pj: String,
    load_pi: String,
    write_pj: String,
    load: String,
    value: String,
    count: String,
    slot_i: usize,
    slot_j: usize,
}

/// An intentionally closed grammar: exactly one allocation, loop, free and
/// load; exactly two integer writes; no call or pointer-valued memory access.
fn certificate(graph: &Graph, load: &str) -> Option<Certificate> {
    let operations = |op: &str| {
        graph
            .nodes
            .values()
            .filter(|n| n.op == op)
            .map(|n| n.eclass.clone())
            .collect::<BTreeSet<_>>()
    };
    if !operations("Call").is_empty()
        || operations("Alloc").len() != 1
        || operations("DoWhile").len() != 1
        || operations("Function").len() != 1
    {
        return None;
    }
    let bops = |tag: &str| {
        graph
            .nodes
            .values()
            .filter(|n| n.op == "Bop" && graph.tagged(&graph.nodes[&n.children[0]].eclass, tag))
            .map(|n| n.eclass.clone())
            .collect::<BTreeSet<_>>()
    };
    let writes: BTreeSet<String> = graph
        .nodes
        .values()
        .filter(|n| n.op == "Top")
        .map(|n| n.eclass.clone())
        .collect();
    if bops("Load").len() != 1 || bops("Free").len() != 1 || writes.len() != 2 {
        return None;
    }
    for w in &writes {
        let row = graph.operator(w, "Top", "Write")?;
        if !graph.int_pointer(&row[0]) || !graph.scalar_type(&row[1], "IntT") {
            return None;
        }
    }
    let function = graph.nodes.values().find(|n| n.op == "Function")?;
    if graph.tuple_signature(&graph.nodes[&function.children[1]].eclass)? != ["IntT", "IntT", "IntT", "StateT"]
        || graph.tuple_signature(&graph.nodes[&function.children[2]].eclass)? != ["StateT"] { return None; }
    // The closed profile admits only the source's built-in expression forms.
    // Type/analysis rows are not executable forms. Calls and pointer memory
    // have separate checks above and below.
    for node in graph.nodes.values().filter(|n| n.eclass.starts_with("Expr-")) {
        if !matches!(node.op.as_str(), "Arg"|"Const"|"Empty"|"Single"|"Concat"|"Get"|"SubTuple"|"Uop"|"Bop"|"Top"|"Alloc"|"If"|"DoWhile"|"Function"|"Print") {
            // Only constructors have Expr-valued eclasses; functions such as
            // ExtractedExprCache are canonical aliases and must not be used
            // as execution edges. Their names are explicitly admitted here.
            if !matches!(node.op.as_str(), "ExtractedExpr"|"ExtractedExprCache"|"TermGet"|"TermBop"|"TermTop"|"TermUop"|"TermAlloc"|"TermPrint"|"TermIf"|"TermDoWhile"|"TermConcat"|"TermSingle"|"TermArg"|"TermConst"|"TermEmpty"|"TermSubTuple") { return None; }
        }
    }
    let load_row = graph.operator(load, "Bop", "Load")?;
    let second = graph.operator(&load_row[1], "Top", "Write")?;
    let first = graph.operator(&second[2], "Top", "Write")?;
    if first[0] != load_row[0] || first[0] == second[0] {
        return None;
    }
    let context = graph.relation_value("ContextOf", load)?;
    for expr in [&first[0], &second[0], &first[1], &first[2]] {
        if graph.relation_value("ContextOf", expr)? != context {
            return None;
        }
    }
    let value = graph.project(load, 0)?;
    if !graph.scalar_type(&value, "IntT") || !graph.scalar_type(&first[1], "IntT") {
        return None;
    }
    let inner = graph.unique(&context, "InIf")?;
    if !graph.tagged(&inner[0], "true") {
        return None;
    }
    let (inner_arg, slot_i) = graph.binding(&first[0], &context)?;
    let (other_arg, slot_j) = graph.binding(&second[0], &context)?;
    if inner_arg != other_arg || slot_i == slot_j {
        return None;
    }
    let loop_arg = inner[2].clone();
    let arg = graph.unique(&loop_arg, "Arg")?;
    let loop_context = arg[1].clone();
    let loop_row = graph.unique(&loop_context, "InLoop")?;
    let loop_expr = operations("DoWhile").into_iter().next()?;
    if graph.unique(&loop_expr, "DoWhile")? != loop_row {
        return None;
    }
    let loop_pi = graph.project(&loop_arg, slot_i)?;
    let loop_pj = graph.project(&loop_arg, slot_j)?;
    if graph.project(&loop_row[1], slot_i + 1)? != loop_pi
        || graph.project(&loop_row[1], slot_j + 1)? != loop_pj
    {
        return None;
    }
    if !graph.int_pointer(&loop_pi) || !graph.int_pointer(&loop_pj) {
        return None;
    }
    let branch_pi = graph.project(&loop_row[0], slot_i)?;
    let branch_pj = graph.project(&loop_row[0], slot_j)?;
    let pi = graph.operator(&branch_pi, "Bop", "PtrAdd")?;
    let pj = graph.operator(&branch_pj, "Bop", "PtrAdd")?;
    if pi[0] != pj[0] {
        return None;
    }
    let shifted_i = graph.operator(&pi[1], "Bop", "Add")?;
    let shifted_j = graph.operator(&pj[1], "Bop", "Add")?;
    if shifted_i[1] != shifted_j[1] || graph.literal(&shifted_i[1]) != Some(1) {
        return None;
    }
    let branch = graph.relation_value("ContextOf", &branch_pi)?;
    if graph.relation_value("ContextOf", &branch_pj)? != branch {
        return None;
    }
    let false_if = graph.unique(&branch, "InIf")?;
    if !graph.tagged(&false_if[0], "false") {
        return None;
    }
    let masked_eq = graph.operator(&false_if[1], "Bop", "Eq")?;
    let mask_i = graph.operator(&masked_eq[0], "Bop", "Bitand")?;
    let mask_j = graph.operator(&masked_eq[1], "Bop", "Bitand")?;
    if mask_i[1] != mask_j[1] || graph.literal(&mask_i[1]) != Some(1) {
        return None;
    }
    let masked_context = graph.relation_value("ContextOf", &false_if[1])?;
    let x = graph.word(&shifted_i[0], &branch, 0)?;
    let y = graph.word(&shifted_j[0], &branch, 0)?;
    if x == y || !matches!((&x,&y),(Word::Slot(a,_),Word::Slot(b,_)) if a==b) {
        return None;
    }
    let mask_words = (
        graph.word(&mask_i[0], &masked_context, 0)?,
        graph.word(&mask_j[0], &masked_context, 0)?,
    );
    if mask_words != (x.clone(), y.clone()) && mask_words != (y.clone(), x.clone()) {
        return None;
    }
    let valid_if = graph.unique(&masked_context, "InIf")?;
    if !graph.tagged(&valid_if[0], "true") {
        return None;
    }
    let guard_context = graph.relation_value("ContextOf", &valid_if[1])?;
    let guards = graph.true_guards(&valid_if[1], &guard_context, 0)?;
    if guards.len() != 6 {
        return None;
    }
    for word in [&x, &y] {
        if !guards.contains(&("GreaterEq".to_owned(), word.clone(), Word::Literal(0)))
            || !guards.contains(&("LessThan".to_owned(), word.clone(), Word::Literal(2)))
        {
            return None;
        }
    }
    let iterations = guards
        .iter()
        .filter(|(op, a, b)| op == "LessEq" && *b == Word::Literal(1_000_000) && a != &x && a != &y)
        .map(|(_, a, _)| a)
        .collect::<Vec<_>>();
    if iterations.len() != 1
        || !guards.contains(&(
            "GreaterEq".to_owned(),
            iterations[0].clone(),
            Word::Literal(0),
        ))
    {
        return None;
    }
    let allocation = operations("Alloc").into_iter().next()?;
    let allocation_row = graph.unique(&allocation, "Alloc")?;
    if graph.literal(&allocation_row[1]) != Some(3)
        || !graph.unique(&allocation_row[3], "PointerT").is_some_and(|p| p.len()==1 && graph.tagged(&p[0], "IntT"))
        || graph.project(&allocation, 0)? != pi[0]
    {
        return None;
    }
    if graph.relation_value("ContextOf", &allocation)? != branch
        || graph.project(&loop_row[0], 0)? != graph.project(&allocation, 1)?
    {
        return None;
    }
    let free = graph.operator(bops("Free").iter().next()?, "Bop", "Free")?;
    let free_state = graph.project(&loop_expr, 0)?;
    if free[1] != free_state || graph.relation_value("ContextOf", &free[0])? != branch {
        return None;
    }
    let base_slots = graph
        .gets
        .iter()
        .filter(|((tuple, _), values)| tuple == &loop_row[0] && values.contains(&pi[0]))
        .map(|((_, i), _)| *i)
        .collect::<Vec<_>>();
    if base_slots.len() != 1 {
        return None;
    }
    let base_slot = base_slots[0];
    if graph.project(&loop_row[1], base_slot + 1)? != graph.project(&loop_arg, base_slot)?
        || graph.project(&loop_expr, base_slot)? != free[0]
    {
        return None;
    }
    let branch_regions = graph
        .nodes
        .values()
        .filter(|n| n.op == "If")
        .filter(|n| {
            graph.nodes[&n.children[0]].eclass == false_if[1]
                && graph.nodes[&n.children[1]].eclass == false_if[2]
        })
        .collect::<Vec<_>>();
    if !branch_regions
        .iter()
        .any(|n| graph.reachable(&graph.nodes[&n.children[3]].eclass, &loop_expr))
        || !graph.reachable(&loop_row[1], load)
    {
        return None;
    }
    let inner_regions = graph.nodes.values().filter(|n| n.op == "If" && n.children.len()==4)
        .filter(|n| graph.nodes[&n.children[0]].eclass == inner[1] && graph.nodes[&n.children[1]].eclass == inner[2])
        .filter(|n| graph.reachable(&loop_row[1], &n.eclass) && graph.reachable(&graph.nodes[&n.children[2]].eclass, load)).count();
    if inner_regions == 0 { return None; }
    // Free must be outside the loop; all mutable operations inside it are the
    // two typed integer writes and load already checked above.
    if graph.reachable(&loop_row[1], bops("Free").iter().next()?) {
        return None;
    }
    for n in graph.nodes.values().filter(|n| n.op == "Function") {
        let root = graph.nodes[&n.children[3]].eclass.clone();
        if !graph.reachable(&root, &loop_expr) || !graph.reachable(&root, &allocation) {
            return None;
        }
    }
    Some(Certificate {
        branch,
        loop_context,
        target_context: context,
        loop_expr,
        allocation,
        base: pi[0].clone(),
        local_i: shifted_i[0].clone(),
        local_j: shifted_j[0].clone(),
        branch_pi,
        branch_pj,
        loop_pi,
        loop_pj,
        load_pi: first[0].clone(),
        write_pj: second[0].clone(),
        load: load.to_owned(),
        value,
        count: first[1].clone(),
        slot_i,
        slot_j,
    })
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Mode {
    Off,
    SeedOnly,
    SeedOff,
    PrimitiveOnly,
    Manual,
    Encoding,
    ReverseOff,
    ShiftOff,
    CellOff,
    QueryOff,
    BridgeOff,
    TransportOff,
    ConsumerOff,
    IndexRescue,
    ShiftRescue,
    CellRescue,
    BranchRescue,
}
impl Mode {
    fn from_env() -> Result<Self, Error> {
        Ok(
            match std::env::var("EGGCC_ALIAS_MODE")
                .as_deref()
                .unwrap_or("off")
            {
                "off" => Self::Off,
                "seed-only" => Self::SeedOnly,
                "seed-off" => Self::SeedOff,
                "primitive-only" => Self::PrimitiveOnly,
                "manual" => Self::Manual,
                "encoding" => Self::Encoding,
                "reverse-off" => Self::ReverseOff,
                "shift-forward-off" => Self::ShiftOff,
                "cell-forward-off" => Self::CellOff,
                "query-off" => Self::QueryOff,
                "bridge-off" => Self::BridgeOff,
                "transport-off" => Self::TransportOff,
                "consumer-off" => Self::ConsumerOff,
                "index-rescue" => Self::IndexRescue,
                "shift-rescue" => Self::ShiftRescue,
                "cell-rescue" => Self::CellRescue,
                "branch-alias-rescue" => Self::BranchRescue,
                other => {
                    return Err(Error::BackendError(format!(
                        "unknown EGGCC_ALIAS_MODE {other}"
                    )))
                }
            },
        )
    }
}

/// Independent finite closure over the exact prematerialized application rows.
/// Values: i,j,one,region,mask-i,mask-j,shift-i,shift-j,cell-i,cell-j.
fn manual(
    reverse: bool,
    shift: bool,
    cell: bool,
    rescue: Option<(usize, usize)>,
) -> ([bool; 3], bool) {
    let rows = [
        ("Mask", vec![0, 2], 4, false),
        ("Mask", vec![1, 2], 5, false),
        ("Shift1", vec![0], 6, shift),
        ("Shift1", vec![1], 7, shift),
        ("Cell", vec![3, 6], 8, cell),
        ("Cell", vec![3, 7], 9, cell),
    ];
    let mut equality = (0..10).collect::<Vec<_>>();
    let mut neq = BTreeSet::from([(4, 5)]);
    if let Some(pair) = rescue {
        neq.insert(pair);
    }
    loop {
        let before = (equality.clone(), neq.clone());
        for (an, ac, ao, am) in &rows {
            for (bn, bc, bo, _) in &rows {
                if an != bn {
                    continue;
                }
                let pairs = if ac.iter().zip(bc).all(|(a, b)| equality[*a] == equality[*b]) {
                    vec![(*ao, *bo)]
                } else if *am && equality[*ao] == equality[*bo] {
                    ac.iter().zip(bc).map(|(a, b)| (*a, *b)).collect()
                } else {
                    vec![]
                };
                for (a, b) in pairs {
                    let old = equality[b];
                    let new = equality[a];
                    for v in &mut equality {
                        if *v == old {
                            *v = new
                        }
                    }
                }
            }
        }
        neq = neq
            .into_iter()
            .map(|(a, b)| {
                let (a, b) = (equality[a], equality[b]);
                (a.min(b), a.max(b))
            })
            .collect();
        for (an, ac, ao, am) in &rows {
            for (bn, bc, bo, _) in &rows {
                if an != bn {
                    continue;
                }
                let (a, b) = (equality[*ao], equality[*bo]);
                let output = (a.min(b), a.max(b));
                for (i, (a, b)) in ac.iter().zip(bc).enumerate() {
                    let (a, b) = (equality[*a], equality[*b]);
                    let child = (a.min(b), a.max(b));
                    if *am && neq.contains(&child) {
                        neq.insert(output);
                    }
                    if reverse
                        && neq.contains(&output)
                        && ac
                            .iter()
                            .zip(bc)
                            .enumerate()
                            .all(|(j, (a, b))| i == j || equality[*a] == equality[*b])
                    {
                        neq.insert(child);
                    }
                }
            }
        }
        if before == (equality.clone(), neq.clone()) {
            break;
        }
    }
    (
        [(0, 1), (6, 7), (8, 9)].map(|(a, b)| {
            let (a, b) = (equality[a], equality[b]);
            neq.contains(&(a.min(b), a.max(b)))
        }),
        neq.iter().any(|(a, b)| a == b),
    )
}

/// The logical rows are instantiated from the revalidated demand certificate.
/// Class labels name opaque equality-sort inputs; they are never primitive
/// semantic comparisons or a substitute for the false masked-Eq seed.
#[derive(Clone)]
struct Imported {
    labels: [String; 4],
    metadata: Vec<(&'static str, i64, i64)>,
    source_seed: bool,
}
impl Imported {
    fn read(graph: &Graph, cert: &Certificate) -> Option<Self> {
        let pi = graph.operator(&cert.branch_pi, "Bop", "PtrAdd")?;
        let pj = graph.operator(&cert.branch_pj, "Bop", "PtrAdd")?;
        let si = graph.operator(&pi[1], "Bop", "Add")?;
        let sj = graph.operator(&pj[1], "Bop", "Add")?;
        let branch = graph.unique(&cert.branch, "InIf")?;
        let eq = graph.operator(&branch[1], "Bop", "Eq")?;
        let mi = graph.operator(&eq[0], "Bop", "Bitand")?;
        let mj = graph.operator(&eq[1], "Bop", "Bitand")?;
        let allocation = graph.unique(&cert.allocation, "Alloc")?;
        let size = graph.literal(&allocation[1])?;
        Some(Self {
            labels: [cert.local_i.clone(),cert.local_j.clone(),si[1].clone(),cert.allocation.clone()],
            metadata: vec![("mask",graph.literal(&mi[1])?,graph.literal(&mj[1])?),
                ("shift",graph.literal(&si[1])?,graph.literal(&sj[1])?),
                // The certificate independently reconstructed these exact
                // signed guard bounds for both imported source words.
                ("lower",0,0),("upper",2,2),("allocation-length",size,size),
                ("access-width-from-IntT",8,8)],
            source_seed: graph.tagged(&branch[0], "false"),
        })
    }
}
fn prove(mode: Mode, imported: &Imported) -> Result<([bool; 3], Json), Error> {
    let reverse = !matches!(mode,Mode::ReverseOff|Mode::IndexRescue|Mode::ShiftRescue|Mode::CellRescue);
    let shift = !matches!(mode,Mode::ShiftOff|Mode::ShiftRescue|Mode::CellRescue);
    let cell = !matches!(mode,Mode::CellOff|Mode::CellRescue);
    let rescue = match mode {Mode::IndexRescue=>Some((0,1)),Mode::ShiftRescue=>Some((6,7)),Mode::CellRescue=>Some((8,9)),_=>None};
    let ids = imported.labels.iter().enumerate().map(|(i,label)| imported.labels.iter().position(|other|other==label).unwrap_or(i)).collect::<Vec<_>>();
    let mut program = format!("(datatype A1Word)\n(datatype A1Region)\n(datatype A1Cell)\n(constructor A1Opaque (i64) A1Word)\n(constructor A1OpaqueRegion (i64) A1Region)\n(constructor A1Mask (A1Word A1Word) A1Word)\n(constructor A1Shift (A1Word) A1Word {})\n(constructor A1Location (A1Region A1Word) A1Cell {})\n(let $a1-left (A1Opaque {}))\n(let $a1-right (A1Opaque {}))\n(let $a1-one (A1Opaque {}))\n(let $a1-region (A1OpaqueRegion {}))\n(let $a1-ml (A1Mask $a1-left $a1-one))\n(let $a1-mr (A1Mask $a1-right $a1-one))\n(let $a1-sl (A1Shift $a1-left))\n(let $a1-sr (A1Shift $a1-right))\n(let $a1-cl (A1Location $a1-region $a1-sl))\n(let $a1-cr (A1Location $a1-region $a1-sr))\n",if shift {":injective"}else{""},if cell {":injective"}else{""},ids[0],ids[1],ids[2],ids[3]);
    if imported.source_seed && mode != Mode::SeedOff {program.push_str("(disequal $a1-ml $a1-mr)\n");}
    if let Some(pair)=rescue {program.push_str(match pair {(0,1)=>"(disequal $a1-left $a1-right)\n",(6,7)=>"(disequal $a1-sl $a1-sr)\n",_=>"(disequal $a1-cl $a1-cr)\n"});}
    let primitive_comparisons = if mode==Mode::PrimitiveOnly {imported.metadata.iter().map(|(field,left,right)|json!({"field":field,"left":left,"right":right,"equal":left==right})).collect::<Vec<_>>()}else{vec![]};
    let mut graph=new_experimental_egraph_with_options(false,DisequalityEncoding::Nee);
    graph.parse_and_run_program(None,&program)?;
    let mut known=[false;3];let mut bottom=false;let mut oracle=None;
    if mode==Mode::Manual {let result=manual(reverse,shift,cell,rescue);known=result.0;bottom=result.1;oracle=Some(result.0);}
    else if !matches!(mode,Mode::SeedOnly|Mode::PrimitiveOnly) {
        graph.parse_and_run_program(None,"(run-schedule (saturate injectivity))")?;
        bottom=match graph.parse_and_run_program(None,"(check-contradiction)"){Ok(_)=>true,Err(Error::CheckError(..))=>false,Err(e)=>return Err(e)};
        if !bottom {for (index,(a,b)) in [("$a1-left","$a1-right"),("$a1-sl","$a1-sr"),("$a1-cl","$a1-cr")].into_iter().enumerate() {
            if index==2 && mode==Mode::QueryOff {continue;}
            let name=format!("A1Known{index}");let predicate=if reverse {"known-disequal?"}else{"known-disequal-forward-only?"};
            graph.parse_and_run_program(None,&format!("(relation {name} ())\n(ruleset {name}-query)\n(rule (({predicate} {a} {b})) (({name})) :ruleset {name}-query :naive)\n(run-schedule (run {name}-query))"))?;
            known[index]=graph.get_size(&name)>0;
        }}
    }
    if bottom {known=[false;3];}
    Ok((known,json!({"program":program,"imported_host_classes":imported.labels,"source_seed":imported.source_seed,"index_known":known[0],"shift_known":known[1],"cell_known":known[2],"bottom":bottom,"reverse_enabled":reverse,"shift_marked":shift,"cell_marked":cell,"same_graph_and_seed":mode!=Mode::SeedOff,"primitive_comparisons":primitive_comparisons,"primitive_mismatch_count":imported.metadata.iter().filter(|(_,a,b)|a!=b).count(),"manual_known":oracle,"query_status":if mode==Mode::QueryOff {"not-run"}else if known[2] {"proved"}else{"unknown-or-error"}})))
}

pub(crate) fn apply(egraph: &mut EGraph, pass: usize) -> Result<(), Error> {
    if pass != 0 {
        return Ok(());
    }
    let mode = Mode::from_env()?;
    let mut receipt = json!({"mode":format!("{mode:?}"),"pass":pass,"status":"off","queries":[],"exports":0,"token_after":0,"consumer_kind":"new demand-scoped copy of existing commute action; existing store-forward rule"});
    if mode != Mode::Off {
        let graph = Graph::read(egraph)?;
        let loads = graph
            .nodes
            .values()
            .filter(|n| n.op == "Bop" && graph.tagged(&graph.nodes[&n.children[0]].eclass, "Load"))
            .map(|n| n.eclass.clone())
            .collect::<BTreeSet<_>>();
        let candidates = loads
            .iter()
            .filter_map(|load| certificate(&graph, load))
            .collect::<Vec<_>>();
        receipt["status"] = json!("unsupported-or-ambiguous-profile");
        if let [cert] = candidates.as_slice() {
            let imported = Imported::read(&graph, cert).ok_or_else(|| Error::BackendError("A1 import certificate mismatch".to_owned()))?;
            let (known, mut query) = prove(mode, &imported)?;
            let branch_alias = (known[2] || mode == Mode::BranchRescue)
                && !matches!(mode, Mode::BridgeOff | Mode::SeedOnly | Mode::PrimitiveOnly);
            let transport = branch_alias && mode != Mode::TransportOff;
            query["branch_alias"] = json!(branch_alias);
            query["loop_alias"] = json!(transport);
            query["demand_alias"] = json!(transport);
            query["certificate"] = json!({"branch":cert.branch,"loop_context":cert.loop_context,"target_context":cert.target_context,"allocation":cert.allocation,"base":cert.base,"local_indices":[cert.local_i,cert.local_j],"branch_pair":[cert.branch_pi,cert.branch_pj],"loop_pair":[cert.loop_pi,cert.loop_pj],"consumer_pair":[cert.write_pj,cert.load_pi],"pointer_slots":[cert.slot_i,cert.slot_j],"both_invariant":true,"load":cert.load,"loaded_value":cert.value,"replacement":cert.count,"guard":"true And of exact six signed comparisons","bounds":[0,2],"shift":1,"allocation_length":3,"element":"i64","access_width_bytes":8,"free_after_loop":true,"no_call_or_pointer_memory":true});
            let fresh = Graph::read(egraph)?;
            if certificate(&fresh, &cert.load).as_ref() != Some(cert) {
                return Err(Error::BackendError(
                    "A1 certificate changed before export".to_owned(),
                ));
            }
            if transport {
                let value = |class: &str| {
                    egraph.class_id_to_value(&egraph_serialize::ClassId::from(class.to_owned()))
                };
                let (write, load_ptr, load, context) = (
                    value(&cert.write_pj),
                    value(&cert.load_pi),
                    value(&cert.load),
                    value(&cert.target_context),
                );
                egraph.update(|mut state| {
                    state.add("A1CommuteDemand", (write, load_ptr, load, context))?;
                    Ok(())
                })?;
                query["token_before"] = json!(egraph.get_size("A1CommuteDemand"));
                let application = if mode != Mode::ConsumerOff {
                    egraph
                        .parse_and_run_program(None, "(run-schedule (run a1-one-shot-commute))")
                        .map(|_| ())
                } else {
                    Ok(())
                };
                // Retire the sole scope-dependent capability before any other
                // ruleset can observe the action's newly merged classes.
                egraph.clear_function("A1CommuteDemand")?;
                application?;
                if mode != Mode::ConsumerOff {
                    egraph.parse_and_run_program(None, "(run-schedule (run mem-simple))")?;
                    egraph.parse_and_run_program(
                        None,
                        &format!("(run-schedule {})", crate::schedule::types_and_indexing()),
                    )?;
                }
            }
            let after = Graph::read(egraph)?;
            let forwarded = after.project(&cert.load, 0).as_deref() == Some(cert.count.as_str())
                || {
                    // Class labels may change after the legitimate loaded-value
                    // union; resolve both old current Values through the engine.
                    let sort = egraph
                        .get_sort_by_name("Expr")
                        .ok_or_else(|| Error::BackendError("A1 missing Expr sort".to_owned()))?;
                    let old_count = egraph
                        .class_id_to_value(&egraph_serialize::ClassId::from(cert.count.clone()));
                    let old_value = egraph
                        .class_id_to_value(&egraph_serialize::ClassId::from(cert.value.clone()));
                    egraph.value_to_class_id(&sort, old_count)
                        == egraph.value_to_class_id(&sort, old_value)
                };
            query["forwarded"] = json!(forwarded);
            query["token_after"] = json!(egraph.get_size("A1CommuteDemand"));
            receipt["status"] = json!("admitted");
            receipt["exports"] = json!(usize::from(transport));
            receipt["queries"] = json!([query]);
            receipt["token_after"] = json!(egraph.get_size("A1CommuteDemand"));
        }
    }
    if let Ok(directory) = std::env::var("EGGCC_ALIAS_EVIDENCE") {
        let path = Path::new(&directory);
        std::fs::create_dir_all(path).map_err(|e| Error::BackendError(e.to_string()))?;
        let output = path.join("boundary-0000.json");
        if output.exists() {
            return Err(Error::BackendError(format!(
                "refusing to overwrite {}",
                output.display()
            )));
        }
        std::fs::write(output, serde_json::to_vec_pretty(&receipt).unwrap())
            .map_err(|e| Error::BackendError(e.to_string()))?;
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn a1_generic_causal_controls() {
        for mode in [
            Mode::Encoding,
            Mode::Manual,
            Mode::SeedOnly,
            Mode::PrimitiveOnly,
            Mode::ReverseOff,
            Mode::ShiftOff,
            Mode::CellOff,
            Mode::QueryOff,
            Mode::BridgeOff,
            Mode::TransportOff,
            Mode::ConsumerOff,
            Mode::IndexRescue,
            Mode::ShiftRescue,
            Mode::CellRescue,
        ] {
            let fixture: Json = serde_json::from_str(include_str!("scoped_alias_graph.json")).unwrap();
            let graph = Graph::from_json(fixture).unwrap();
            let cert = certificate(&graph,"Expr-297").unwrap();
            let imported = Imported::read(&graph,&cert).unwrap();
            let (known, receipt) = prove(mode, &imported).unwrap();
            assert_eq!(
                known[2],
                matches!(
                    mode,
                    Mode::Encoding
                        | Mode::Manual
                        | Mode::BridgeOff
                        | Mode::TransportOff
                        | Mode::ConsumerOff
                        | Mode::IndexRescue
                        | Mode::ShiftRescue
                        | Mode::CellRescue
                ),
                "{receipt}"
            );
            assert_eq!(receipt["bottom"], false);
        }
    }
    #[test]
    fn a1_manual_stages_and_rescues() {
        assert_eq!(manual(true, true, true, None).0, [true, true, true]);
        assert_eq!(manual(false, true, true, None).0, [false, false, false]);
        assert_eq!(manual(true, false, true, None).0, [true, false, false]);
        assert_eq!(manual(true, true, false, None).0, [true, true, false]);
        assert_eq!(
            manual(false, true, true, Some((0, 1))).0,
            [true, true, true]
        );
        assert_eq!(
            manual(false, false, true, Some((6, 7))).0,
            [false, true, true]
        );
    }
    #[test]
    fn a1_guard_and_type_rejection() {
        let graph = Graph::from_json(json!({"nodes":{}})).unwrap();
        assert!(certificate(&graph, "missing").is_none());
        assert!(graph.word("missing", "wrong-context", 0).is_none());
        assert!(graph.true_guards("missing", "wrong-context", 0).is_none());
    }

    #[test]
    fn a1_retained_graph_certificate_and_transport_boundaries() {
        let fixture: Json = serde_json::from_str(include_str!("scoped_alias_graph.json")).unwrap();
        let graph = Graph::from_json(fixture.clone()).unwrap();
        let load = graph
            .nodes
            .values()
            .find(|n| n.op == "Bop" && graph.tagged(&graph.nodes[&n.children[0]].eclass, "Load"))
            .unwrap()
            .eclass
            .clone();
        let cert = certificate(&graph, &load).expect("retained A1 certificate");
        assert_eq!((cert.slot_i, cert.slot_j), (5, 6));
        let loop_row = graph.unique(&cert.loop_context, "InLoop").unwrap();
        for slot in [cert.slot_i, cert.slot_j] {
            let mut changed = Graph::from_json(fixture.clone()).unwrap();
            changed.gets.insert(
                (loop_row[1].clone(), slot + 1),
                BTreeSet::from(["Expr-unproved-update".to_owned()]),
            );
            assert!(
                certificate(&changed, &load).is_none(),
                "one invariant is insufficient"
            );
        }
        for op in ["Call", "Alloc"] {
            let mut changed = Graph::from_json(fixture.clone()).unwrap();
            changed.nodes.insert(
                "a1-extra-effect".to_owned(),
                Node {
                    op: op.to_owned(),
                    children: vec![],
                    eclass: "Expr-extra-effect".to_owned(),
                },
            );
            assert!(certificate(&changed, &load).is_none());
        }
        for (original, replacement) in [("GreaterEq", "UnsupportedGuard"), ("IntT", "FloatT")] {
            let mut changed = fixture.clone();
            for node in changed["nodes"].as_object_mut().unwrap().values_mut() {
                if node["op"] == original {
                    node["op"] = json!(replacement)
                }
            }
            assert!(certificate(&Graph::from_json(changed).unwrap(), &load).is_none());
        }
        let mut collapsed = fixture.clone();
        for node in collapsed["nodes"].as_object_mut().unwrap().values_mut() {
            if node["eclass"] == cert.write_pj {
                node["eclass"] = json!(cert.load_pi)
            }
        }
        assert!(certificate(&Graph::from_json(collapsed).unwrap(), &load).is_none());
    }

    #[test]
    fn a1_one_shot_matches_existing_commute_and_forward() {
        let setup="(let ctx (InFunc \"a1-action-parity\"))\n(let ty (TupleT (TCons (PointerT (IntT)) (TCons (PointerT (IntT)) (TCons (StateT) (TNil))))))\n(let arg (Arg ty ctx))\n(let pa (Get arg 0))\n(let pb (Get arg 1))\n(let state (Get arg 2))\n(let value (Const (Int 9) ty ctx))\n(let zero (Const (Int 0) ty ctx))\n(let first (Top (Write) pa value state))\n(let second (Top (Write) pb zero first))\n(let load (Bop (Load) pa second))\n(let observed (Get load 0))\n(ContextOf pa ctx)\n(ContextOf pb ctx)\n(ContextOf load ctx)\n";
        for scoped in [false, true] {
            let mut graph = new_experimental_egraph_with_options(false, DisequalityEncoding::Nee);
            graph
                .parse_and_run_program(None, &crate::prologue())
                .unwrap();
            graph.parse_and_run_program(None, setup).unwrap();
            if scoped {
                graph.parse_and_run_program(None,"(A1CommuteDemand pb pa load ctx)\n(run-schedule (run a1-one-shot-commute))").unwrap();
                graph.clear_function("A1CommuteDemand").unwrap();
            } else {
                graph
                    .parse_and_run_program(None, "(NoAlias pb pa)")
                    .unwrap();
            }
            graph
                .parse_and_run_program(
                    None,
                    "(run-schedule (repeat 2 mem-simple))\n(check (= observed value))",
                )
                .unwrap();
            assert_eq!(graph.get_size("A1CommuteDemand"), 0);
        }
    }
    #[test]
    fn a1_seed_bottom_and_certificate_semantic_negatives() {
        let fixture: Json=serde_json::from_str(include_str!("scoped_alias_graph.json")).unwrap();
        let graph=Graph::from_json(fixture.clone()).unwrap();
        let cert=certificate(&graph,"Expr-297").unwrap();
        let imported=Imported::read(&graph,&cert).unwrap();
        assert_eq!(prove(Mode::SeedOff,&imported).unwrap().0,[false;3]);
        let mut absent=imported.clone();absent.source_seed=false;
        assert_eq!(prove(Mode::Encoding,&absent).unwrap().0,[false;3]);
        let mut collapse=imported.clone();collapse.labels[1]=collapse.labels[0].clone();
        let (known,receipt)=prove(Mode::Encoding,&collapse).unwrap();
        assert_eq!(known,[false;3]);assert_eq!(receipt["bottom"],true);
        let (_,null)=prove(Mode::PrimitiveOnly,&imported).unwrap();
        assert_eq!(null["primitive_comparisons"].as_array().unwrap().len(),6);
        assert_eq!(null["primitive_mismatch_count"],0);
        for op in ["Bitand","GreaterEq","LessThan","LessEq","Free","PointerT"] {
            let mut bad=fixture.clone();
            for node in bad["nodes"].as_object_mut().unwrap().values_mut() {if node["op"]==op {node["op"]=json!("A1Unsupported");}}
            assert!(certificate(&Graph::from_json(bad).unwrap(),"Expr-297").is_none(),"{op}");
        }
        let mut changed=Graph::from_json(fixture.clone()).unwrap();
        changed.gets.insert((cert.loop_expr.clone(),0),BTreeSet::from(["Expr-foreign-state".to_owned()]));
        assert!(certificate(&changed,"Expr-297").is_none());
        let mut changed=Graph::from_json(fixture).unwrap();
        for node in changed.nodes.values_mut().filter(|n|n.op=="If") {
            if node.children.len()==4 && graph.nodes[&node.children[0]].eclass==graph.unique(&cert.target_context,"InIf").unwrap()[1] {node.children.swap(2,3);}
        }
        assert!(certificate(&changed,"Expr-297").is_none());
    }

}
