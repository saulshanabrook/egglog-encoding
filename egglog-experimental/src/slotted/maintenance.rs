//! Invariant maintenance, emitted independently of user rewrites.
use super::model::*;
use super::syntax::quote;

/// Generated commands carry their declarations so the frontend can reserve
/// encoding names without parsing the rules and initial facts a second time.
#[derive(Default)]
pub(super) struct Generated {
    pub source: String,
    pub declarations: Vec<String>,
}

impl Generated {
    fn push(&mut self, command: String) {
        if !self.source.is_empty() {
            self.source.push('\n');
        }
        self.source.push_str(&command);
    }

    fn declare(&mut self, kind: &str, name: &str, tail: String) {
        self.push(format!("({kind} {name} {tail})"));
        self.declarations.push(name.to_owned());
    }
}

pub(super) const MACHINERY: &str = "(seq (saturate (seq (saturate (seq (saturate (run slotted)) (run slotted-empty) (run slotted-restore))) (saturate (run slotted-migrate)) (saturate (seq (saturate (run slotted-group)) (run slotted-shrink) (run slotted-restore))) (run slotted-shape))) (saturate (run slotted-read)))";

pub(super) fn schedule(steps: usize, has_rules: bool) -> String {
    if steps == 0 || !has_rules {
        return format!("(run-schedule {MACHINERY})");
    }
    format!(
        "(run-schedule {MACHINERY} (repeat {steps} (seq (run) (saturate (run slotted-refine)) (run slotted-apply) {MACHINERY})))"
    )
}

pub(super) fn shared() -> Generated {
    let mut s = include_str!("templates/shared.egg").to_owned();
    for i in 0..512 {
        s.push_str(&format!("(GroupIdx {i})\n"));
    }
    for i in 0..8 {
        s.push_str(&format!("(GroupIdxSmall {i})\n"));
    }
    Generated {
        source: s,
        declarations: [
            "GroupIdx",
            "GroupIdxSmall",
            "Idx",
            "slotted-refine",
            "slotted",
            "slotted-migrate",
            "slotted-group",
            "slotted-empty",
            "slotted-shrink",
            "slotted-restore",
            "slotted-shape",
            "slotted-read",
            "slotted-apply",
            "SlottedNodeLayout",
            "SlottedEdgeLayout",
            "SlottedBinderLayout",
            "SlottedPayloadLayout",
            "SlottedCarrierLayout",
            "SlottedSlotLayout",
        ]
        .map(str::to_owned)
        .into(),
    }
}

pub(super) fn carrier(s: &Symbols, proofs: bool) -> Generated {
    let invocation_decl = if proofs {
        format!(
            "(relation {} ({} Renaming {}))",
            s.invocation, s.sort, s.sort
        )
    } else {
        format!(
            "(function {} ({} Renaming) {} :merge ((union old new) old))",
            s.invocation, s.sort, s.sort
        )
    };
    let invocation_register = if proofs {
        format!("({} _c _name _a)", s.invocation)
    } else {
        format!("(set ({} _c _name) _a)", s.invocation)
    };
    let invocation_union = if proofs {
        format!(
            "(rule (({} _c _name _a) ({} _c _name _b) (!= _a _b)) ((union _a _b)) :ruleset slotted :name \"slotted/invocation-merge/{}\")",
            s.invocation, s.invocation, s.index
        )
    } else {
        String::new()
    };
    // Database-owned memo rows follow push/pop and rebuild their output class.
    // Proof substitution has its own explicit reconstruction path.
    let substitution_memo = if proofs {
        String::new()
    } else {
        format!(
            "(function SubstMemoClass_{} (String) {} :merge old)\n(function SubstMemoFrame_{} (String) Renaming :merge old)",
            s.free_vars, s.sort, s.free_vars
        )
    };
    let source = format!(
        include_str!("templates/carrier.egg"),
        sort = s.sort,
        sort_name = quote(&s.sort),
        renames = s.renames,
        equated = s.equated,
        free_vars = s.free_vars,
        subst_pending = s.subst_pending,
        shape_equal = s.shape_equal,
        invocation_decl = invocation_decl,
        invocation_register = invocation_register,
        invocation_union = invocation_union,
        substitution_memo = substitution_memo,
        index = s.index,
        group_replace = format!("GroupReplace_{}", s.index),
        group = s.group,
        coset_reps = s.coset_reps,
        big_reading = s.big_reading,
        reading = s.reading
    );
    let mut declarations = vec![
        s.sort.clone(),
        s.renames.clone(),
        s.equated.clone(),
        s.free_vars.clone(),
        s.subst_pending.clone(),
        s.shape_equal.clone(),
        s.invocation.clone(),
        s.group.clone(),
        format!("GroupReplace_{}", s.index),
        s.coset_reps.clone(),
        s.big_reading.clone(),
        s.reading.clone(),
    ];
    if !proofs {
        declarations.extend([
            format!("SubstMemoClass_{}", s.free_vars),
            format!("SubstMemoFrame_{}", s.free_vars),
        ]);
    }
    Generated {
        source,
        declarations,
    }
}

pub(super) fn constructor(op: &Constructor, s: &Symbols, proofs: bool) -> Generated {
    let name = &op.name;
    let n = op.children().len();
    let cols = op.types();
    // Emit the machinery namespace directly; source/global names must never
    // become variables in these rules. Declaration names are left unchanged.
    let edges = names("_m", n);
    let kids = names("_c", n);
    let pays = names("_p", op.columns.len() - n);
    let node = op.node(name, &edges, &kids, &pays);
    let slots = fold(
        "map-union",
        edges.iter().map(|m| format!("(map-image {m})")),
        "(map-empty)",
    );
    let mut out = Generated::default();
    out.declare("constructor", name, format!("({cols}) {}", s.sort));
    let mut physical = 0;
    let mut edge_cols = Vec::new();
    for col in &op.columns {
        match col {
            Column::Payload(sort) => {
                out.push(format!(
                    "(set (SlottedPayloadLayout \"{name}\" {physical} \"{sort}\") ())"
                ));
                physical += 1;
            }
            _ => {
                edge_cols.push(physical);
                let layout = if *col == Column::Child {
                    "SlottedEdgeLayout"
                } else {
                    "SlottedSlotLayout"
                };
                out.push(format!("(set ({layout} \"{name}\" {physical}) ())"));
                physical += if *col == Column::Child { 2 } else { 1 };
            }
        }
    }
    out.push(format!(
        "(set (SlottedNodeLayout \"{name}\" {physical}) ())"
    ));
    if let Some(covered) = op.covered() {
        for b in op.binders() {
            out.push(format!(
                "(set (SlottedBinderLayout \"{name}\" {} {} -1 \"\") ())",
                edge_cols[b], edge_cols[covered]
            ));
        }
    }
    out.push(format!(
        "(rule ((= _e1 {node})) ((set ({} _e1) {slots})) :ruleset slotted :name \"slotted/class-slots/{name}\")",
        s.free_vars
    ));
    if n == 0 {
        return out;
    }
    let groups = op
        .children()
        .iter()
        .enumerate()
        .map(|(i, column)| {
            if **column == Column::Child {
                format!("_g{}", i + 1)
            } else {
                "(set-of (map-of 0 0))".into()
            }
        })
        .collect::<Vec<String>>();
    let shapes = names("_s", n);
    let group_facts = groups
        .iter()
        .zip(&kids)
        .zip(op.children())
        .filter(|(_, column)| **column == Column::Child)
        .map(|((g, k), _)| format!("(= {g} ({} {k}))", s.group))
        .collect::<Vec<_>>()
        .join(" ");
    let cache_types = vec!["Renaming Group"; n].join(" ");
    let cache = |es: &[String]| {
        call(
            &format!("_shapeof_{name}"),
            es.iter()
                .zip(&groups)
                .flat_map(|(e, g)| [e.clone(), g.clone()]),
        )
    };
    let cached = cache(&edges);
    out.declare(
        "function",
        &format!("_pinned_{name}"),
        format!("({cols} i64) Renaming :merge new"),
    );
    let canonical = (0..n)
        .map(|i| format!("(vec-get _sh {i})"))
        .collect::<Vec<_>>();
    let shape_outputs = (0..=n)
        .map(|i| format!("(vec-get _sh {i})"))
        .collect::<Vec<_>>()
        .join(" ");
    let other = names("_n", n);
    let other_node = op.node(name, &other, &kids, &pays);
    if proofs {
        // Key rebuilding may retain different old rows in the two tables. The
        // selected back renaming must therefore be part of the class lookup.
        let class_key = |edges: &[String], back: &str| {
            let mut key = op.node(&format!("_shape_class_{name}"), edges, &kids, &pays);
            key.pop();
            key.push_str(&format!(" {back})"));
            key
        };
        out.declare(
            "function",
            &format!("_shape_class_{name}"),
            format!("({cols} Renaming) {} :merge old", s.sort),
        );
        out.declare(
            "function",
            &format!("_shape_back_{name}"),
            format!("({cols}) Renaming :merge old"),
        );
        out.declare(
            "function",
            &format!("_shapeof_edges_{name}"),
            format!("({cache_types}) Renamings :no-merge"),
        );
        out.declare(
            "function",
            &format!("_shapeof_syms_{name}"),
            format!("({cache_types}) Group :no-merge"),
        );
        let indexed_class = class_key(&canonical, &format!("(vec-get _sh {n})"));
        let back_key = op.node(&format!("_shape_back_{name}"), &canonical, &kids, &pays);
        let cached_edges = cached.replace("_shapeof_", "_shapeof_edges_");
        let cached_syms = cached.replace("_shapeof_", "_shapeof_syms_");
        out.push(format!("(rule ((= _c {node}) {group_facts} (= _sh (node-shape (vec-of {}) (vec-of {})))) ((set {indexed_class} _c) (set {back_key} (vec-get _sh {n})) (set {cached_edges} (vec-of {shape_outputs})) (set {cached_syms} (symmetries-of _sh {}))) :ruleset slotted-shape :name \"slotted/shape-index/{name}\")", edges.join(" "), groups.join(" "), n+1));
        out.push(format!("(rule ((= _c {node}) {group_facts} (= _syms {cached_syms}) (= _cs ({} _c))) ((set ({} _c) (group-restrict _syms _cs))) :ruleset slotted-group :name \"slotted/node-symmetry/{name}\")", s.free_vars, s.group));
        let unpacked = shapes
            .iter()
            .enumerate()
            .map(|(i, v)| format!("(= {v} (vec-get _sh {i}))"))
            .collect::<Vec<_>>()
            .join(" ");
        let stored_class = class_key(&shapes, "_back0");
        let back_key = op.node(&format!("_shape_back_{name}"), &shapes, &kids, &pays);
        out.push(format!("(rule ((= _c {node}) {group_facts} (= _sh {cached_edges}) {unpacked} (= _back (vec-get _sh {n})) (= _c0 {stored_class}) (= _back0 {back_key}) (guard (or (bool-!= _c _c0) (bool-!= _back _back0)))) ((set ({} _c (compose _back (inverse _back0)) _c0) ())) :ruleset slotted-shape :name \"slotted/shape-collision/{name}\")", s.shape_equal));
        let other_cached = cache(&other).replace("_shapeof_", "_shapeof_edges_");
        let equal = (0..n)
            .map(|i| format!("(= (vec-get _sh1 {i}) (vec-get _sh2 {i}))"))
            .collect::<Vec<_>>()
            .join(" ");
        out.push(format!("(rule ((= _c {node}) {group_facts} (= _sh1 {cached_edges}) (= _c {other_node}) (= _sh2 {other_cached}) {equal} (= _v1 (vec-of {})) (= _v2 (vec-of {})) (!= _v1 _v2) (= _v1 (ordering-max _v1 _v2))) ((set ({} _c (compose (vec-get _sh1 {n}) (inverse (vec-get _sh2 {n}))) _c) ()) (delete {node})) :ruleset slotted-shape :name \"slotted/shape-dedup/{name}\")", edges.join(" "), other.join(" "), s.shape_equal));
    } else {
        let key = op.node(&format!("_shape_{name}"), &canonical, &kids, &pays);
        out.declare("function", &format!("_shape_{name}"), format!("({cols}) ({} Renaming) :merge ((set ({} old0 (compose old1 (inverse new1)) new0) ()) (values old0 old1))",s.sort,s.shape_equal));
        out.declare(
            "function",
            &format!("_shapeof_{name}"),
            format!(
                "({cache_types}) ({} Group) :no-merge",
                vec!["Renaming"; n + 1].join(" ")
            ),
        );
        out.push(format!("(rule ((= _c {node}) {group_facts} (= _sh (node-shape (vec-of {}) (vec-of {})))) ((set {key} (values _c (vec-get _sh {n}))) (set {cached} (values {shape_outputs} (symmetries-of _sh {})))) :ruleset slotted-shape :name \"slotted/shape-index/{name}\")",edges.join(" "),groups.join(" "),n+1));
        out.push(format!("(rule ((= _c {node}) {group_facts} (= (values {} _back _syms) {cached}) (= _cs ({} _c))) ((set ({} _c) (group-restrict _syms _cs))) :ruleset slotted-group :name \"slotted/node-symmetry/{name}\")",shapes.join(" "),s.free_vars,s.group));
        let other_cached = cache(&other);
        out.push(format!("(rule ((= _c {node}) {group_facts} (= (values {} _b1 _syms1) {cached}) (= _c {other_node}) (= (values {} _b2 _syms2) {other_cached}) (= _v1 (vec-of {})) (= _v2 (vec-of {})) (!= _v1 _v2) (= _v1 (ordering-max _v1 _v2))) ((delete {node})) :ruleset slotted-shape :name \"slotted/shape-dedup/{name}\")",shapes.join(" "),shapes.join(" "),edges.join(" "),other.join(" ")));
    }
    let node_cols = &node[name.len() + 2..node.len() - 1];
    for j in 0..n {
        if op.children()[j] != &Column::Child {
            continue;
        }
        let pinned = fold(
            "map-union",
            edges
                .iter()
                .enumerate()
                .filter(|(i, _)| *i != j)
                .map(|(_, e)| format!("(map-image {e})")),
            "(map-empty)",
        );
        out.push(format!("(rule ((= _row {node}) (= _grp ({} {})) (= _pinned (map-domain (compose {pinned} {})))) ((set (_pinned_{name} {node_cols} {}) _pinned) (set ({} {} _pinned) (group-coset-reps _grp _pinned))) :ruleset slotted-read :name \"slotted/coset-readings/{name}/{j}\")",s.group,kids[j],edges[j],j+1,s.coset_reps,kids[j]));
    }
    let moved = op.node(name, &other, &kids, &pays);
    let pulls = other
        .iter()
        .zip(&edges)
        .map(|(a, b)| format!("(= {a} (compose _R {b}))"))
        .collect::<Vec<_>>()
        .join(" ");
    out.push(format!("(rule (({} _e2 _m _e1) (= _e2 {node}) (!= _e1 _e2) (= _e2 (ordering-max _e1 _e2)) (= _nodeslots {slots}) (= _R (find-mapping-total (map-domain _m) _nodeslots (map-domain _m) _m)) {pulls}) ((union _e1 {moved}) (delete {node})) :ruleset slotted-migrate :name \"slotted/migration/{name}\")",s.renames));
    for pos in 0..n {
        if op.children()[pos] != &Column::Child {
            continue;
        }
        let mut es = edges.clone();
        let mut ks = kids.clone();
        es[pos] = format!("(compose {} _m)", edges[pos]);
        ks[pos] = "_c'".into();
        let new = op.node(name, &es, &ks, &pays);
        let child = &kids[pos];
        let edge = &edges[pos];
        out.push(format!("(rule (({} {child} _m _c') (= _node {node}) (= {child} (ordering-max {child} _c')) (guard (or (bool-!= {child} _c') (bool= (compose _m _m) _m))) (guard (or (bool-!= {child} _c') (bool-!= (compose {edge} _m) {edge})))) ((union _node {new}) (delete {node})) :ruleset slotted-migrate :name \"slotted/child-update/{name}/{pos}\")",s.renames));
    }
    if let Some(covered) = op.covered() {
        let binders = op.binders();
        let mut es = edges.clone();
        let ks = kids.clone();
        for (i, &pos) in binders.iter().enumerate() {
            es[pos] = format!("_mvar{i}");
        }
        let bound_node = op.node(name, &es, &ks, &pays);
        let uncovered = (0..n)
            .filter(|i| !binders.contains(i) && *i != covered)
            .collect::<Vec<_>>();
        let all_slots = es
            .iter()
            .skip(1)
            .fold(format!("(map-image {})", es[0]), |a, e| {
                format!("(map-union {a} (map-image {e}))")
            });
        for (i, &pos) in binders.iter().enumerate() {
            let free = uncovered
                .iter()
                .map(|&u| format!("(map-not-contains (map-image {}) _v{i})", edges[u]))
                .collect::<Vec<_>>()
                .join(" ");
            out.push(format!("(rule (({} {bound_node} _ml _l) (= _v{i} (map-get _mvar{i} 0)) {free}) (({} {bound_node} (inverse (map-remove (inverse _ml) _v{i})) _l)) :ruleset slotted :name \"slotted/binder-strip/{name}/{pos}\")",s.renames,s.equated));
            for &u in &uncovered {
                let mut fresh = es.clone();
                fresh[pos] = format!("(map-of 0 _w{i})");
                fresh[covered] = format!(
                    "(compose (map-insert (map-image {}) _v{i} _w{i}) {})",
                    edges[covered], edges[covered]
                );
                let renamed = op.node(name, &fresh, &ks, &pays);
                out.push(format!("(rule ((= _node {bound_node}) (= _v{i} (map-get _mvar{i} 0)) (map-contains (map-image {}) _v{i}) (= _used {all_slots}) (= _fresh{i} (find-mapping-total _used (map-of 0 0) (map-empty) (map-empty))) (= _w{i} (map-get _fresh{i} 0))) ((union _node {renamed}) (delete {bound_node})) :ruleset slotted :name \"slotted/binder-refresh/{name}/{pos}/{u}\")",edges[u]));
            }
        }
    }
    out
}

#[cfg(test)]
#[path = "maintenance/tests.rs"]
mod tests;
