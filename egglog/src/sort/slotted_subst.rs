//! `slotted-subst`: substitution for the slotted e-graph encoding.
//!
//! `(slotted-subst body x var t_ren t [class_slots])` replaces, inside `body`, the variable
//! sitting at slot `x` of `body`'s frame with the invocation `t_ren * t`, and
//! returns a class spelled in `body`'s frame whose slots are
//! `(slots(body) \ {x}) ∪ im(t_ren)`.
//!
//! A slotted node's children occupy two columns each — a `Renaming` naming the
//! child's slots in the node's frame, then the child class. The compiler publishes
//! the complete physical node and edge layout in hidden Unit-valued functions, so
//! this primitive never guesses which erased `Id` columns are edges. Input-language
//! container columns are outside the slotted front end's current contract; the
//! metadata nevertheless makes every supported constructor layout explicit.
//!
//! # One term, not a sub-e-graph
//!
//! This extracts a single smallest term rooted at `body`, substitutes in that
//! term, and adds the result back — matching the reference implementation's
//! `ExtractionSubst`. It is deliberately not a copy of the whole reachable
//! sub-e-graph: the classes the substitution does not touch are shared with the
//! original, and a class where `x` cannot occur is returned untouched.
//!
//! Extraction is cost-based, so a class whose only e-nodes refer back to itself
//! has no finite term. Substituting under such a class returns no value rather
//! than looping. A primitive that returns nothing from an *action* is a program
//! error in egglog, so that is what the caller sees.
//!
//! # Binders
//!
//! Binder metadata identifies each marker edge and the one child edge it covers.
//! Markers are node data rather than AST children: they contribute no extraction
//! cost and are never traversed as terms. Rebuilding alpha-refreshes their private
//! names and changes only their covered edge. That both stops substitution below a
//! binder which shadows `x` and prevents a free slot of the replacement from being
//! captured, matching the reference representation's `Bind<T>` and fresh private
//! slots.
//!
//! # `Context::Full`
//!
//! The extraction reads live table contents and the rebuild writes rows, so
//! this is a `FullPrim`: callable from top-level actions and from the head of a
//! `:naive` rule only. As with any read of live state from an action, `body`
//! must already have rows — a term the enclosing action just built is not there
//! to be extracted, and neither is a node the encoding's compression has moved
//! onto another member of `body`'s class.

use super::*;
use crate::exec_state::RegistrySealed;
use egglog_bridge::{TableAction, TableKind};
use hashbrown::HashMap;
use std::collections::{BTreeMap, BTreeSet};

/// The name of the primitive, as written in an egglog program.
pub const SLOTTED_SUBST: &str = "slotted-subst";

/// The name of the companion that answers the same call's renaming.
pub const SLOTTED_SUBST_FRAME: &str = "slotted-subst-frame";

/// A slot name, as a renaming spells it.
type Slot = i64;

/// A renaming: a partial injection on slot names.
type Ren = BTreeMap<Slot, Slot>;

/// The slot the primitive's contract fixes for `var`: the variable class is
/// `(Var 0)`, so "the variable at slot `s`" is `var` reached by an edge
/// `0 -> s`.
const VAR_SLOT: Slot = 0;

const NODE_LAYOUT: &str = "SlottedNodeLayout";
const EDGE_LAYOUT: &str = "SlottedEdgeLayout";
const BINDER_LAYOUT: &str = "SlottedBinderLayout";
const CLASS_SLOTS: &str = "ClassSlots";

/// One child edge, at its physical renaming column in the constructor.
#[derive(Clone, Debug)]
struct Edge {
    col: usize,
    ren: Ren,
    child: Value,
}

/// One active binder in an e-node row.
#[derive(Clone, Copy, Debug)]
struct Binder {
    marker: usize,
    covered: usize,
}

/// One e-node, ready to be rebuilt in another frame.
#[derive(Clone, Debug)]
struct Node {
    ctor: String,
    args: Vec<Value>,
    edges: Vec<Edge>,
    binders: Vec<Binder>,
}

impl Node {
    fn children(&self) -> impl Iterator<Item = Value> + '_ {
        self.edges
            .iter()
            .filter(|edge| !self.binders.iter().any(|binder| binder.marker == edge.col))
            .map(|edge| edge.child)
    }
}

#[derive(Clone, Debug)]
struct BinderLayout {
    marker: usize,
    covered: usize,
    discriminator: Option<(usize, Value)>,
}

#[derive(Clone, Debug)]
struct Layout {
    arity: usize,
    edges: Vec<usize>,
    binders: Vec<BinderLayout>,
}

#[derive(Default)]
struct Layouts {
    constructors: HashMap<String, Layout>,
}

/// The e-nodes reachable from a root, with the smallest-term choice for each
/// class.
struct Terms {
    nodes: HashMap<Value, Vec<Node>>,
    /// The e-node of each class that roots its smallest term, as an index into
    /// `nodes`. A class with no finite term is absent.
    best: HashMap<Value, usize>,
}

/// `edge` carried into the frame `m` names, leaving alone the slots `m` does
/// not cover.
///
/// A node may carry a slot its class does not — a redundant slot, which the
/// encoding permits — so `m`, defined on the class's slots, need not cover
/// every slot the node's edges point at. Composing would drop those entries
/// and misstate which slots the child has.
fn carry(m: &Ren, edge: &Ren) -> Ren {
    edge.iter()
        .map(|(k, v)| (*k, m.get(v).copied().unwrap_or(*v)))
        .collect()
}

/// The identity renaming on `m`'s image.
fn image(m: &Ren) -> Ren {
    m.values().map(|v| (*v, *v)).collect()
}

fn rename_image(m: &mut Ren, from: Slot, to: Slot) {
    for value in m.values_mut() {
        if *value == from {
            *value = to;
        }
    }
}

/// Deterministic alpha-fresh names for one primitive invocation.
///
/// Both result halves perform the rebuild independently, so freshness cannot use a
/// global counter: the class-producing and frame-producing calls must choose the same
/// names. The smallest nonnegative name absent from the extracted term, its ambient
/// frames, and the replacement is stable across both calls.
struct Fresh {
    used: BTreeSet<Slot>,
    next: Slot,
}

impl Fresh {
    fn new(used: BTreeSet<Slot>) -> Self {
        Self { used, next: 0 }
    }

    fn take(&mut self) -> Option<Slot> {
        loop {
            let candidate = self.next;
            self.next = self.next.checked_add(1)?;
            if self.used.insert(candidate) {
                return Some(candidate);
            }
        }
    }
}

/// Substitute `t_ren * t` for the variable at slot `x` of `body`'s frame.
///
/// `var` is the class every variable lives in; `x` names the slot in `body`'s
/// own frame. Returns the result as an invocation -- the class, and the renaming
/// carrying its slots into `body`'s frame -- because the result is not always a
/// freshly built node: a body that cannot name `x` comes back as itself, and the
/// variable itself comes back as `t`, each under the renaming it was reached by.
/// `None` when `body` has no finite term, so nothing can be substituted into.
fn substitute(
    state: &mut FullState<'_, '_>,
    body: Value,
    x: Slot,
    var: Value,
    t_ren: &Ren,
    t: Value,
    class_slots: &str,
) -> Result<Option<(Value, Ren)>, String> {
    let layouts = Layouts::load(state, class_slots)?;
    let terms = collect_terms(state, body, var, &layouts)?;
    if !terms.best.contains_key(&body) {
        return Ok(None);
    }

    // A class can hold nodes with redundant slots, so the chosen node's edge
    // images are only an upper bound. `ClassSlots` is the encoding's exact public
    // frame and is therefore required at the root.
    let frame = class_slots_if_present(state, class_slots, body)?
        .ok_or_else(|| format!("{class_slots} has no row for the substitution body"))?;
    if frame.iter().any(|(from, to)| from != to) {
        return Err(format!(
            "{class_slots} returned a non-identity slot set for {body:?}: {frame:?}"
        ));
    }

    let mut used = BTreeSet::from([x]);
    used.extend(frame.keys().chain(frame.values()).copied());
    used.extend(t_ren.keys().chain(t_ren.values()).copied());
    for nodes in terms.nodes.values() {
        for node in nodes {
            for edge in &node.edges {
                used.extend(edge.ren.keys().chain(edge.ren.values()).copied());
            }
        }
    }

    let mut rebuild = Rebuild {
        terms,
        x,
        var,
        t_ren: t_ren.clone(),
        t,
        memo: HashMap::new(),
        fresh: Fresh::new(used),
        class_slots: class_slots.to_owned(),
    };
    Ok(rebuild.go(state, body, frame))
}

struct Rebuild {
    terms: Terms,
    x: Slot,
    var: Value,
    t_ren: Ren,
    t: Value,
    memo: HashMap<(Value, Ren), (Value, Ren)>,
    fresh: Fresh,
    class_slots: String,
}

impl Rebuild {
    /// Substitute inside `c`, whose slots `m` carries into `body`'s frame.
    /// Returns the resulting class and the renaming carrying its slots into
    /// that same frame.
    fn go(&mut self, state: &mut FullState<'_, '_>, c: Value, m: Ren) -> Option<(Value, Ren)> {
        // Slot `x` is not among the slots this subterm can name, so no
        // occurrence of the substituted variable is under it.
        if !m.values().any(|slot| *slot == self.x) {
            return Some((c, m));
        }
        if c == self.var && m.get(&VAR_SLOT) == Some(&self.x) {
            return Some((self.t, self.t_ren.clone()));
        }
        if let Some(hit) = self.memo.get(&(c, m.clone())) {
            return Some(hit.clone());
        }

        // The chosen e-node's cost strictly exceeds its children's, so the
        // recursion terminates even where the e-graph is cyclic.
        let node = self.terms.nodes[&c][*self.terms.best.get(&c)?].clone();
        let mut args = node.args.clone();
        let mut slots = Ren::new();

        // Binder markers are data, not AST children. Give every active binder a
        // fresh private name, and apply that alpha-renaming only to the edge it
        // covers. An uncovered sibling using the old spelling remains free.
        let mut refreshed = Vec::with_capacity(node.binders.len());
        for binder in &node.binders {
            let marker = node.edges.iter().find(|edge| edge.col == binder.marker)?;
            let old = *marker.ren.get(&VAR_SLOT)?;
            let fresh = self.fresh.take()?;
            let marker_ren = BTreeMap::from([(VAR_SLOT, fresh)]);
            args[binder.marker] = intern(state, &marker_ren);
            args[binder.marker + 1] = self.var;
            refreshed.push((*binder, old, fresh));
        }

        for edge in &node.edges {
            if refreshed
                .iter()
                .any(|(binder, _, _)| binder.marker == edge.col)
            {
                continue;
            }

            let mut child_frame = carry(&m, &edge.ren);
            for (binder, old, fresh) in &refreshed {
                if binder.covered == edge.col {
                    rename_image(&mut child_frame, *old, *fresh);
                }
            }
            let (child, ren) = self.go(state, edge.child, child_frame)?;
            let mut child_slots = image(&ren);
            for (binder, _, fresh) in &refreshed {
                if binder.covered == edge.col {
                    child_slots.remove(fresh);
                }
            }
            slots.extend(child_slots);
            args[edge.col] = intern(state, &ren);
            args[edge.col + 1] = child;
        }
        let out = match state.add(&node.ctor, RawValues(args)) {
            Ok(out) => out,
            Err(err) => {
                log::error!("{SLOTTED_SUBST}: rebuilding {}: {err}", node.ctor);
                return None;
            }
        };
        match class_slots_if_present(state, &self.class_slots, out) {
            Ok(Some(existing)) => slots.retain(|slot, _| existing.contains_key(slot)),
            Ok(None) => {}
            Err(err) => {
                log::error!("{SLOTTED_SUBST}: reading rebuilt class slots: {err}");
                return None;
            }
        }
        self.memo.insert((c, m), (out, slots.clone()));
        Some((out, slots))
    }
}

/// Intern a renaming as a `Renaming` value.
fn intern(state: &mut FullState<'_, '_>, ren: &Ren) -> Value {
    let data: BTreeMap<Value, Value> = ren
        .iter()
        .map(|(k, v)| {
            (
                state.base_to_value::<i64>(*k),
                state.base_to_value::<i64>(*v),
            )
        })
        .collect();
    state.container_to_value(MapContainer::renaming(data))
}

/// The e-nodes reachable from `root`, and each class's smallest-term choice.
// One `eclass_enodes` call per reachable class, and that scans every
// constructor table: an output-column index, or one grouped pass over every
// table, would replace this loop without changing the result.
fn collect_terms(
    state: &FullState<'_, '_>,
    root: Value,
    var: Value,
    layouts: &Layouts,
) -> Result<Terms, String> {
    let mut nodes: HashMap<Value, Vec<Node>> = HashMap::new();
    let mut stack = vec![root];
    while let Some(eclass) = stack.pop() {
        if nodes.contains_key(&eclass) {
            continue;
        }
        let mut rows: Vec<(String, Vec<Value>)> = Vec::new();
        state
            .eclass_enodes(eclass, |enode| {
                if !enode.subsumed {
                    rows.push((enode.name.to_owned(), enode.children.to_vec()));
                }
            })
            .map_err(|err| format!("reading the e-nodes of {eclass:?}: {err}"))?;
        let parsed: Vec<Node> = rows
            .into_iter()
            .map(|(ctor, children)| parse_node(state, layouts, var, ctor, &children))
            .collect::<Result<_, _>>()?;
        stack.extend(parsed.iter().flat_map(Node::children));
        nodes.insert(eclass, parsed);
    }

    Ok(Terms {
        best: cheapest(&nodes),
        nodes,
    })
}

/// The e-node rooting each class's smallest term, by term size. A class with no
/// finite term is absent, and the choice does not depend on iteration order.
// A least fixpoint rather than a walk: a class can hold an e-node that refers
// back to itself, and only a cost that has to come from somewhere rules those
// out. Ties keep the incumbent, over a fixed class order.
fn cheapest(nodes: &HashMap<Value, Vec<Node>>) -> HashMap<Value, usize> {
    let mut order: Vec<Value> = nodes.keys().copied().collect();
    order.sort_unstable();

    let mut cost: HashMap<Value, u64> = HashMap::new();
    let mut best: HashMap<Value, usize> = HashMap::new();
    loop {
        let mut changed = false;
        for eclass in &order {
            for (index, node) in nodes[eclass].iter().enumerate() {
                let mut total: u64 = 1;
                let mut finite = true;
                for child in node.children() {
                    match cost.get(&child) {
                        Some(child_cost) => total = total.saturating_add(*child_cost),
                        None => {
                            finite = false;
                            break;
                        }
                    }
                }
                if finite && cost.get(eclass).is_none_or(|prev| total < *prev) {
                    cost.insert(*eclass, total);
                    best.insert(*eclass, index);
                    changed = true;
                }
            }
        }
        if !changed {
            return best;
        }
    }
}

/// Decode a constructor row from the compiler-emitted physical layout.
fn parse_node(
    state: &FullState<'_, '_>,
    layouts: &Layouts,
    var: Value,
    ctor: String,
    children: &[Value],
) -> Result<Node, String> {
    let layout = layouts
        .constructors
        .get(&ctor)
        .ok_or_else(|| format!("reachable constructor {ctor} has no {NODE_LAYOUT} row"))?;
    if layout.arity != children.len() {
        return Err(format!(
            "constructor {ctor} has {} runtime inputs but metadata says {}",
            children.len(),
            layout.arity
        ));
    }

    let mut edges = Vec::with_capacity(layout.edges.len());
    for &col in &layout.edges {
        edges.push(Edge {
            col,
            ren: decode_renaming(state, children[col])?,
            child: children[col + 1],
        });
    }

    let mut binders = Vec::new();
    for binder in &layout.binders {
        if binder
            .discriminator
            .is_some_and(|(col, expected)| children[col] != expected)
        {
            continue;
        }
        let marker = edges
            .iter()
            .find(|edge| edge.col == binder.marker)
            .expect("validated binder marker edge");
        if marker.child != var || marker.ren.len() != 1 || !marker.ren.contains_key(&VAR_SLOT) {
            return Err(format!(
                "constructor {ctor} binder marker at column {} must be {{0 -> slot}} * var",
                binder.marker
            ));
        }
        binders.push(Binder {
            marker: binder.marker,
            covered: binder.covered,
        });
    }

    Ok(Node {
        ctor,
        args: children.to_vec(),
        edges,
        binders,
    })
}

fn decode_renaming(state: &FullState<'_, '_>, value: Value) -> Result<Ren, String> {
    let map = state
        .value_to_container::<MapContainer>(value)
        .ok_or_else(|| format!("metadata marks {value:?} as a Renaming, but it is not a Map"))?;
    if map.rebuilds_contents() {
        return Err("a slotted edge Renaming may contain only base slot values".to_owned());
    }
    let ren: Ren = map
        .data
        .iter()
        .map(|(k, v)| {
            (
                state.value_to_base::<i64>(*k),
                state.value_to_base::<i64>(*v),
            )
        })
        .collect();
    if ren.values().copied().collect::<BTreeSet<_>>().len() != ren.len() {
        return Err("a slotted edge Renaming must be injective".to_owned());
    }
    Ok(ren)
}

fn live_action(state: &FullState<'_, '_>, name: &str) -> Result<TableAction, String> {
    if !state
        .table_sizes()
        .into_iter()
        .any(|(candidate, _)| candidate == name)
    {
        return Err(format!("required table {name} is not live"));
    }
    state
        .registry()
        .lookup_table(name)
        .cloned()
        .ok_or_else(|| format!("required table {name} is not registered"))
}

fn metadata_rows(
    state: &FullState<'_, '_>,
    name: &str,
    inputs: &[ColumnTy],
) -> Result<Vec<Vec<Value>>, String> {
    let action = live_action(state, name)?;
    let mut expected = inputs.to_vec();
    expected.push(ColumnTy::Base(state.base_values().get_ty::<()>()));
    if action.kind() != TableKind::Function
        || action.input_arity() != inputs.len()
        || action.output_arity() != 1
        || action.schema() != expected
    {
        return Err(format!(
            "{name} has an unsupported schema; proof-encoded or user-replaced metadata is not supported"
        ));
    }
    let mut rows = Vec::new();
    state
        .function_entries(name, |entry| {
            if !entry.subsumed {
                rows.push(entry.inputs.to_vec());
            }
        })
        .map_err(|err| format!("reading {name}: {err}"))?;
    Ok(rows)
}

fn index(value: i64, what: &str) -> Result<usize, String> {
    usize::try_from(value).map_err(|_| format!("{what} must be a nonnegative column index"))
}

fn class_slots_if_present(
    state: &FullState<'_, '_>,
    class_slots: &str,
    class: Value,
) -> Result<Option<Ren>, String> {
    let Some(value) = state
        .lookup(class_slots, RawValues(vec![class]))
        .map_err(|err| format!("reading {class_slots} for {class:?}: {err}"))?
    else {
        return Ok(None);
    };
    let slots = decode_renaming(state, value)?;
    if slots.iter().any(|(from, to)| from != to) {
        return Err(format!(
            "{class_slots} for {class:?} is not an identity map: {slots:?}"
        ));
    }
    Ok(Some(slots))
}

fn validate_class_slots(state: &FullState<'_, '_>, class_slots: &str) -> Result<(), String> {
    let action = live_action(state, class_slots)?;
    if action.kind() != TableKind::Function
        || action.input_arity() != 1
        || action.output_arity() != 1
        || action.schema() != [ColumnTy::Id, ColumnTy::Id]
    {
        return Err(format!(
            "{class_slots} has an unsupported schema; proof-encoded or user-replaced metadata is not supported"
        ));
    }
    Ok(())
}

fn validate_constructor_layout(
    state: &FullState<'_, '_>,
    ctor: &str,
    layout: &Layout,
    string: ColumnTy,
) -> Result<(), String> {
    let action = live_action(state, ctor)?;
    if action.kind() != TableKind::Constructor
        || action.input_arity() != layout.arity
        || action.output_arity() != 1
        || action.schema().get(layout.arity) != Some(&ColumnTy::Id)
    {
        return Err(format!(
            "constructor {ctor} does not have the e-class schema described by {NODE_LAYOUT}"
        ));
    }

    let mut occupied = BTreeSet::new();
    for &edge in &layout.edges {
        let child = edge
            .checked_add(1)
            .ok_or_else(|| format!("{EDGE_LAYOUT} column overflows for {ctor}"))?;
        if child >= layout.arity {
            return Err(format!(
                "{EDGE_LAYOUT} column {edge} for {ctor} has no following child column"
            ));
        }
        if !occupied.insert(edge) || !occupied.insert(child) {
            return Err(format!(
                "overlapping {EDGE_LAYOUT} columns in {ctor} at {edge}/{child}"
            ));
        }
        if action.schema().get(edge) != Some(&ColumnTy::Id)
            || action.schema().get(child) != Some(&ColumnTy::Id)
        {
            return Err(format!(
                "{EDGE_LAYOUT} for {ctor} marks columns {edge}/{child} whose runtime types are not Id"
            ));
        }
    }

    // The slotted source language currently admits only base payloads.  An
    // unoccupied Id column could be an equality-sort or arbitrary container
    // payload; the erased runtime schema cannot distinguish those cases or say
    // how they should be rebuilt, so decline instead of copying an unsound id.
    for col in 0..layout.arity {
        if !occupied.contains(&col) && !matches!(action.schema()[col], ColumnTy::Base(_)) {
            return Err(format!(
                "constructor {ctor} has an unsupported Id payload at column {col}"
            ));
        }
    }

    let mut unconditional_markers = BTreeSet::new();
    let mut exact_binders = BTreeSet::new();
    for binder in &layout.binders {
        if binder.marker >= binder.covered {
            return Err(format!(
                "{BINDER_LAYOUT} for {ctor} must cover an edge after its marker"
            ));
        }
        if !layout.edges.contains(&binder.marker) || !layout.edges.contains(&binder.covered) {
            return Err(format!(
                "{BINDER_LAYOUT} for {ctor} names a column which is not in {EDGE_LAYOUT}"
            ));
        }
        if !exact_binders.insert((binder.marker, binder.covered, binder.discriminator)) {
            return Err(format!("duplicate {BINDER_LAYOUT} row for {ctor}"));
        }
        match binder.discriminator {
            None => {
                if !unconditional_markers.insert(binder.marker) {
                    return Err(format!(
                        "multiple unconditional {BINDER_LAYOUT} rows for {ctor} marker {}",
                        binder.marker
                    ));
                }
            }
            Some((col, _)) => {
                if col >= layout.arity || occupied.contains(&col) {
                    return Err(format!(
                        "{BINDER_LAYOUT} discriminator column {col} for {ctor} is not a payload"
                    ));
                }
                if action.schema().get(col) != Some(&string) {
                    return Err(format!(
                        "{BINDER_LAYOUT} discriminator column {col} for {ctor} is not a String"
                    ));
                }
            }
        }
    }
    for binder in &layout.binders {
        if binder.discriminator.is_some() && unconditional_markers.contains(&binder.marker) {
            return Err(format!(
                "{BINDER_LAYOUT} for {ctor} mixes conditional and unconditional rows for marker {}",
                binder.marker
            ));
        }
    }
    Ok(())
}

impl Layouts {
    fn load(state: &FullState<'_, '_>, class_slots: &str) -> Result<Self, String> {
        let string = ColumnTy::Base(state.base_values().get_ty::<S>());
        let integer = ColumnTy::Base(state.base_values().get_ty::<i64>());

        let mut layouts = Self::default();
        for row in metadata_rows(state, NODE_LAYOUT, &[string, integer])? {
            let ctor = state.value_to_base::<S>(row[0]).into_inner();
            let arity = index(
                state.value_to_base::<i64>(row[1]),
                &format!("{NODE_LAYOUT} arity for {ctor}"),
            )?;
            let previous = layouts.constructors.insert(
                ctor.clone(),
                Layout {
                    arity,
                    edges: Vec::new(),
                    binders: Vec::new(),
                },
            );
            if previous.is_some() {
                return Err(format!("conflicting {NODE_LAYOUT} rows for {ctor}"));
            }
        }
        if layouts.constructors.is_empty() {
            return Err(format!("{NODE_LAYOUT} contains no constructor rows"));
        }

        for row in metadata_rows(state, EDGE_LAYOUT, &[string, integer])? {
            let ctor = state.value_to_base::<S>(row[0]).into_inner();
            let col = index(
                state.value_to_base::<i64>(row[1]),
                &format!("{EDGE_LAYOUT} column for {ctor}"),
            )?;
            let layout = layouts
                .constructors
                .get_mut(&ctor)
                .ok_or_else(|| format!("{EDGE_LAYOUT} names unknown constructor {ctor}"))?;
            if layout.edges.contains(&col) {
                return Err(format!(
                    "duplicate {EDGE_LAYOUT} row for {ctor} column {col}"
                ));
            }
            layout.edges.push(col);
        }

        Self::load_binders(state, string, integer, &mut layouts)?;
        for (ctor, layout) in &mut layouts.constructors {
            layout.edges.sort_unstable();
            layout
                .binders
                .sort_by_key(|binder| (binder.marker, binder.covered, binder.discriminator));
            validate_constructor_layout(state, ctor, layout, string)?;
        }
        validate_class_slots(state, class_slots)?;
        Ok(layouts)
    }

    fn load_binders(
        state: &FullState<'_, '_>,
        string: ColumnTy,
        integer: ColumnTy,
        layouts: &mut Self,
    ) -> Result<(), String> {
        let rows = metadata_rows(
            state,
            BINDER_LAYOUT,
            &[string, integer, integer, integer, string],
        )?;
        for row in rows {
            let ctor = state.value_to_base::<S>(row[0]).into_inner();
            let marker = index(
                state.value_to_base::<i64>(row[1]),
                &format!("{BINDER_LAYOUT} marker for {ctor}"),
            )?;
            let covered = index(
                state.value_to_base::<i64>(row[2]),
                &format!("{BINDER_LAYOUT} covered edge for {ctor}"),
            )?;
            let discriminator_col = state.value_to_base::<i64>(row[3]);
            let discriminator_text = state.value_to_base::<S>(row[4]).into_inner();
            let discriminator = if discriminator_col == -1 {
                if !discriminator_text.is_empty() {
                    return Err(format!(
                        "unconditional {BINDER_LAYOUT} row for {ctor} has a discriminator value"
                    ));
                }
                None
            } else {
                Some((
                    index(
                        discriminator_col,
                        &format!("{BINDER_LAYOUT} discriminator for {ctor}"),
                    )?,
                    row[4],
                ))
            };
            layouts
                .constructors
                .get_mut(&ctor)
                .ok_or_else(|| format!("{BINDER_LAYOUT} names unknown constructor {ctor}"))?
                .binders
                .push(BinderLayout {
                    marker,
                    covered,
                    discriminator,
                });
        }
        Ok(())
    }
}

/// Which half of a substitution's result a primitive answers.
///
/// A substitution's result is an invocation, and a primitive returns one value,
/// so it takes two calls to read one. `slotted-subst` gives the class and
/// `slotted-subst-frame` the renaming; called with the same arguments they
/// describe the same result, and the pair is what the caller wants. The work is
/// repeated, so prefer one call each rather than either in a loop.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum Half {
    /// The result class.
    Class,
    /// The renaming carrying that class's slots into `body`'s frame.
    Frame,
}

/// The `slotted-subst` primitives, for one `Renaming` sort.
#[derive(Clone)]
pub(crate) struct SlottedSubst {
    /// Which half of the result this one answers.
    pub(crate) half: Half,
    /// The `Map i64 i64` sort renamings are values of.
    pub(crate) renaming: ArcSort,
    /// The sort of a slot name: the renaming sort's key sort, `i64`.
    pub(crate) slot: ArcSort,
}

impl Primitive for SlottedSubst {
    fn name(&self) -> &str {
        match self.half {
            Half::Class => SLOTTED_SUBST,
            Half::Frame => SLOTTED_SUBST_FRAME,
        }
    }

    fn get_type_constraints(&self, span: &Span) -> Box<dyn TypeConstraint> {
        Box::new(SlottedSubstTypeConstraint {
            half: self.half,
            name: self.name().to_owned(),
            renaming: self.renaming.clone(),
            slot: self.slot.clone(),
            span: span.clone(),
        })
    }
}

impl FullPrim for SlottedSubst {
    fn apply<'a, 'db>(&self, mut state: FullState<'a, 'db>, args: &[Value]) -> Option<Value> {
        let (body, x, var, t_ren, t, class_slots) = match args {
            [body, x, var, t_ren, t] => (*body, *x, *var, *t_ren, *t, CLASS_SLOTS.to_owned()),
            [body, x, var, t_ren, t, class_slots] => (
                *body,
                *x,
                *var,
                *t_ren,
                *t,
                state.value_to_base::<S>(*class_slots).into_inner(),
            ),
            _ => panic!(
                "{} takes five or six arguments; the typechecker admitted {}",
                self.name(),
                args.len()
            ),
        };
        let x = state.value_to_base::<i64>(x);
        // Cloned out so the container registry is not still borrowed when the
        // rebuild interns new renamings.
        let t_ren: Ren = state
            .value_to_container::<MapContainer>(t_ren)
            .unwrap_or_else(|| {
                panic!(
                    "{}'s type constraint admits only renaming values",
                    self.name()
                )
            })
            .data
            .iter()
            .map(|(k, v)| {
                (
                    state.value_to_base::<i64>(*k),
                    state.value_to_base::<i64>(*v),
                )
            })
            .collect();
        let (class, frame) = match substitute(&mut state, body, x, var, &t_ren, t, &class_slots) {
            Ok(Some(result)) => result,
            Ok(None) => return None,
            Err(err) => {
                log::error!("{}: {err}", self.name());
                return None;
            }
        };
        Some(match self.half {
            Half::Class => class,
            Half::Frame => intern(&mut state, &frame),
        })
    }
}

/// `(slotted-subst body x var t_ren t [class_slots])`, where the optional string
/// names the carrier's class-slot function. The five-argument form uses the legacy
/// `ClassSlots`. `slotted-subst-frame` has the same inputs and a `Renaming` result.
struct SlottedSubstTypeConstraint {
    half: Half,
    name: String,
    renaming: ArcSort,
    slot: ArcSort,
    span: Span,
}

impl TypeConstraint for SlottedSubstTypeConstraint {
    fn get(
        &self,
        arguments: &[AtomTerm],
        typeinfo: &TypeInfo,
    ) -> Vec<Box<dyn Constraint<AtomTerm, ArcSort>>> {
        let (body, x, var, t_ren, t, class_slots, out) = match arguments {
            [body, x, var, t_ren, t, out] => (body, x, var, t_ren, t, None, out),
            [body, x, var, t_ren, t, class_slots, out] => {
                (body, x, var, t_ren, t, Some(class_slots), out)
            }
            _ => {
                return vec![constraint::impossible(
                    constraint::ImpossibleConstraint::ArityMismatch {
                        atom: Atom {
                            span: self.span.clone(),
                            head: self.name.clone(),
                            args: arguments.to_vec(),
                        },
                        expected: if arguments.len() > 6 { 7 } else { 6 },
                    },
                )];
            }
        };

        let mut cs: Vec<Box<dyn Constraint<AtomTerm, ArcSort>>> = vec![
            constraint::assign(x.clone(), self.slot.clone()),
            constraint::assign(t_ren.clone(), self.renaming.clone()),
        ];
        if let Some(class_slots) = class_slots {
            cs.push(constraint::assign(
                class_slots.clone(),
                StringSort.to_arcsort(),
            ));
        }

        // The class arguments share one eq-sort, as does the result when it is
        // the class half; `xor` defers the choice until the surrounding program
        // pins it down.
        let mut shared = vec![body, var, t];
        match self.half {
            Half::Class => shared.push(out),
            Half::Frame => cs.push(constraint::assign(out.clone(), self.renaming.clone())),
        }
        let mut eq_sorts = typeinfo.get_arcsorts_by(|sort| sort.is_eq_sort());
        eq_sorts.sort_by_key(|sort| sort.name().to_owned());
        cs.push(constraint::xor(
            eq_sorts
                .into_iter()
                .map(|sort| {
                    constraint::and(
                        shared
                            .iter()
                            .map(|arg| constraint::assign((*arg).clone(), sort.clone()))
                            .collect(),
                    )
                })
                .collect(),
        ));
        cs
    }
}
