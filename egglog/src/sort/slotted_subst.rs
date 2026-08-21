//! `slotted-subst`: substitution for the slotted e-graph encoding.
//!
//! `(slotted-subst body x var t_ren t)` replaces, inside `body`, the variable
//! sitting at slot `x` of `body`'s frame with the invocation `t_ren * t`, and
//! returns a class spelled in `body`'s frame whose slots are
//! `(slots(body) \ {x}) ∪ im(t_ren)`.
//!
//! A slotted node's children occupy two columns each — a `Renaming` naming the
//! child's slots in the node's frame, then the child class. Any other column is
//! a payload, carrying no slots. Both are recognised from the table schema: a
//! column typed as an id holding a renaming value starts a child, and the
//! column after it is that child's class.
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
//! # Bound slots are not renamed
//!
//! Nothing tells this primitive which of a node's children is a binder, so it
//! substitutes into the extracted term as it stands: a slot in `im(t_ren)` that
//! the term already uses as a bound slot is captured. The caller chooses `t_ren`,
//! so keeping its image clear of the slots `body`'s term binds is the caller's
//! job.
//!
//! This matches the reference implementation rather than falling short of it. Its
//! `do_term_subst` is the same structural walk with no binder handling -- it
//! rebuilds each node and returns `t` where the rebuilt id equals the one being
//! replaced -- so capture is ruled out by how the representation names bound
//! slots, not by renaming them during substitution.
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
use hashbrown::HashMap;
use std::collections::BTreeMap;

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

/// One column of an e-node, after the edge columns have been paired with the
/// children they name.
#[derive(Clone, Debug)]
enum Col {
    /// Carries no slots; copied through unchanged.
    Payload(Value),
    /// A child class and the renaming carrying its slots into the node's frame.
    Edge { ren: Ren, child: Value },
}

/// One e-node, ready to be rebuilt in another frame.
#[derive(Clone, Debug)]
struct Node {
    ctor: String,
    cols: Vec<Col>,
}

impl Node {
    fn children(&self) -> impl Iterator<Item = Value> + '_ {
        self.cols.iter().filter_map(|col| match col {
            Col::Edge { child, .. } => Some(*child),
            Col::Payload(_) => None,
        })
    }
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
) -> Option<(Value, Ren)> {
    let terms = collect_terms(state, body);
    let root = terms.best.get(&body).copied()?;

    // `body` is spelled in its own frame, so the root renaming is the identity
    // on its slots. `var`'s slot set is fixed by the primitive's contract, and
    // is not visible in its e-node.
    let mut frame: Ren = terms.nodes[&body][root]
        .cols
        .iter()
        .filter_map(|col| match col {
            Col::Edge { ren, .. } => Some(image(ren)),
            Col::Payload(_) => None,
        })
        .flatten()
        .collect();
    if body == var {
        frame.insert(VAR_SLOT, VAR_SLOT);
    }

    let mut rebuild = Rebuild {
        terms,
        x,
        var,
        t_ren: t_ren.clone(),
        t,
        memo: HashMap::new(),
    };
    rebuild.go(state, body, frame)
}

struct Rebuild {
    terms: Terms,
    x: Slot,
    var: Value,
    t_ren: Ren,
    t: Value,
    memo: HashMap<(Value, Ren), (Value, Ren)>,
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
        let mut args: Vec<Value> = Vec::with_capacity(node.cols.len());
        let mut slots = Ren::new();
        for col in &node.cols {
            match col {
                Col::Payload(v) => args.push(*v),
                Col::Edge { ren, child } => {
                    let (child, ren) = self.go(state, *child, carry(&m, ren))?;
                    slots.extend(image(&ren));
                    args.push(intern(state, &ren));
                    args.push(child);
                }
            }
        }
        let out = match state.add(&node.ctor, RawValues(args)) {
            Ok(out) => out,
            Err(err) => {
                log::error!("{SLOTTED_SUBST}: rebuilding {}: {err}", node.ctor);
                return None;
            }
        };
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
fn collect_terms(state: &FullState<'_, '_>, root: Value) -> Terms {
    let mut schemas: HashMap<String, Option<Schema>> = HashMap::new();
    let mut nodes: HashMap<Value, Vec<Node>> = HashMap::new();
    let mut stack = vec![root];
    while let Some(eclass) = stack.pop() {
        if nodes.contains_key(&eclass) {
            continue;
        }
        let mut rows: Vec<(String, Vec<Value>)> = Vec::new();
        if let Err(err) = state.eclass_enodes(eclass, |enode| {
            if !enode.subsumed {
                rows.push((enode.name.to_owned(), enode.children.to_vec()));
            }
        }) {
            log::error!("{SLOTTED_SUBST}: reading the e-nodes of {eclass:?}: {err}");
        }
        let parsed: Vec<Node> = rows
            .into_iter()
            .filter_map(|(ctor, children)| parse_node(state, &mut schemas, ctor, &children))
            .collect();
        stack.extend(parsed.iter().flat_map(Node::children));
        nodes.insert(eclass, parsed);
    }

    Terms {
        best: cheapest(&nodes),
        nodes,
    }
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

/// A constructor's key column types, plus whether its output column is an
/// e-class.
struct Schema {
    keys: Vec<ColumnTy>,
    eq_output: bool,
}

/// Pair up an e-node's edge and child columns; `None` for a row that is not a
/// slotted node.
fn parse_node(
    state: &FullState<'_, '_>,
    schemas: &mut HashMap<String, Option<Schema>>,
    ctor: String,
    children: &[Value],
) -> Option<Node> {
    let schema = schemas
        .entry(ctor.clone())
        .or_insert_with(|| schema_of(state, &ctor))
        .as_ref()?;
    // A relation is a constructor table too, but its output column is a unit
    // rather than an e-class, so its rows are not e-nodes.
    if !schema.eq_output || schema.keys.len() != children.len() {
        return None;
    }

    let mut cols = Vec::new();
    let mut i = 0;
    while i < children.len() {
        match renaming_at(state, &schema.keys, children, i) {
            Some(ren) => {
                cols.push(Col::Edge {
                    ren,
                    child: children[i + 1],
                });
                i += 2;
            }
            None => {
                cols.push(Col::Payload(children[i]));
                i += 1;
            }
        }
    }
    Some(Node { ctor, cols })
}

/// The renaming column `i` holds, if column `i` is an edge: it must be typed as
/// an id, hold a renaming value, and be followed by a column typed as an id.
// The column type is what makes this decidable: base values and container
// values are both plain `Value`s, so a payload column can hold the same number
// as a live renaming.
fn renaming_at(
    state: &FullState<'_, '_>,
    keys: &[ColumnTy],
    children: &[Value],
    i: usize,
) -> Option<Ren> {
    if keys[i] != ColumnTy::Id || keys.get(i + 1) != Some(&ColumnTy::Id) {
        return None;
    }
    let map = state.value_to_container::<MapContainer>(children[i])?;
    if map.rebuilds_contents() {
        // Keys or values are e-classes, so this is not a renaming on slots.
        return None;
    }
    Some(
        map.data
            .iter()
            .map(|(k, v)| {
                (
                    state.value_to_base::<i64>(*k),
                    state.value_to_base::<i64>(*v),
                )
            })
            .collect(),
    )
}

fn schema_of(state: &FullState<'_, '_>, ctor: &str) -> Option<Schema> {
    let action = state.registry().lookup_table(ctor)?;
    let keys = action.input_arity();
    Some(Schema {
        keys: action.schema()[..keys].to_vec(),
        eq_output: action.schema().get(keys) == Some(&ColumnTy::Id),
    })
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
        let [body, x, var, t_ren, t] = args else {
            panic!(
                "{} takes five arguments; the typechecker admitted {}",
                self.name(),
                args.len()
            )
        };
        let x = state.value_to_base::<i64>(*x);
        // Cloned out so the container registry is not still borrowed when the
        // rebuild interns new renamings.
        let t_ren: Ren = state
            .value_to_container::<MapContainer>(*t_ren)
            .unwrap_or_else(|| {
                panic!("{}'s type constraint admits only renaming values", self.name())
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
        let (class, frame) = substitute(&mut state, *body, x, *var, &t_ren, *t)?;
        Some(match self.half {
            Half::Class => class,
            Half::Frame => intern(&mut state, &frame),
        })
    }
}

/// `(slotted-subst body x var t_ren t) : (R, i64, R, Renaming, R) -> R`, and
/// `slotted-subst-frame` the same with a `Renaming` result, for any eq-sort `R`.
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
        let [body, x, var, t_ren, t, out] = arguments else {
            return vec![constraint::impossible(
                constraint::ImpossibleConstraint::ArityMismatch {
                    atom: Atom {
                        span: self.span.clone(),
                        head: self.name.clone(),
                        args: arguments.to_vec(),
                    },
                    expected: 6,
                },
            )];
        };

        let mut cs: Vec<Box<dyn Constraint<AtomTerm, ArcSort>>> = vec![
            constraint::assign(x.clone(), self.slot.clone()),
            constraint::assign(t_ren.clone(), self.renaming.clone()),
        ];

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
