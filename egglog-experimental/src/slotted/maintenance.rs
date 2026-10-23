//! Invariant maintenance, emitted independently of user rewrites.
use super::model::*;
use super::syntax::machinery;

pub(super) const MACHINERY: &str = "(seq (saturate (seq (saturate (seq (saturate (run slotted)) (run slotted-empty) (run slotted-restore))) (saturate (run slotted-migrate)) (saturate (seq (saturate (run slotted-group)) (run slotted-shrink) (run slotted-restore))) (run slotted-shape))) (saturate (run slotted-read)))";

pub(super) fn schedule(steps: usize, has_rules: bool) -> String {
    if steps == 0 || !has_rules {
        return format!("(run-schedule {MACHINERY})");
    }
    format!(
        "(run-schedule {MACHINERY} (repeat {steps} (seq (run) (saturate (run slotted-refine)) (run slotted-apply) {MACHINERY})))"
    )
}

pub(super) fn shared() -> String {
    let mut s = include_str!("templates/shared.egg").to_owned();
    for i in 0..512 {
        s.push_str(&format!("(GroupIdx {i})\n"));
    }
    for i in 0..8 {
        s.push_str(&format!("(GroupIdxSmall {i})\n"));
    }
    s
}

pub(super) fn carrier(s: &Symbols) -> String {
    format!(
        include_str!("templates/carrier.egg"),
        sort = s.sort,
        var = s.var,
        renames = s.renames,
        equated = s.equated,
        free_vars = s.free_vars,
        subst_pending = s.subst_pending,
        shape_equal = s.shape_equal,
        invocation = s.invocation,
        group_replace = format!("GroupReplace_{}", s.index),
        group = s.group,
        coset_reps = s.coset_reps,
        big_reading = s.big_reading,
        reading = s.reading
    )
}

pub(super) fn constructor(op: &Constructor, s: &Symbols) -> String {
    let name = &op.name;
    let n = op.children().len();
    let cols = op.types();
    let edges = names("m", n);
    let kids = names("c", n);
    let pays = names("p", op.columns.len() - n);
    let node = op.node(name, &edges, &kids, &pays);
    let slots = fold(
        "map-union",
        edges.iter().map(|m| format!("(map-image {m})")),
        "(map-empty)",
    );
    let mut out = vec![format!("(constructor {name} ({cols}) {})", s.sort)];
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
                out.push(format!(
                    "(set (SlottedEdgeLayout \"{name}\" {physical}) ())"
                ));
                physical += 2;
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
        "(rule ((= e1 {node})) ((set ({} e1) {slots})))",
        s.free_vars
    ));
    if n == 0 {
        return machinery(&out.join("\n"));
    }
    let groups = names("g", n);
    let shapes = names("s", n);
    let group_facts = groups
        .iter()
        .zip(&kids)
        .map(|(g, k)| format!("(= {g} ({} {k}))", s.group))
        .collect::<Vec<_>>()
        .join(" ");
    let cache = |es: &[String]| {
        call(
            &format!("_shapeof_{name}"),
            es.iter()
                .zip(&groups)
                .flat_map(|(e, g)| [e.clone(), g.clone()]),
        )
    };
    let cached = cache(&edges);
    out.push(format!("(function _shape_{name} ({cols}) ({} Renaming) :merge ((set ({} old0 (compose old1 (inverse new1)) new0) ()) (values old0 old1)))",s.sort,s.shape_equal));
    out.push(format!(
        "(function _shapeof_{name} ({}) ({} Group) :no-merge)",
        vec!["Renaming Group"; n].join(" "),
        vec!["Renaming"; n + 1].join(" ")
    ));
    out.push(format!(
        "(function _pinned_{name} ({cols} i64) Renaming :merge new)"
    ));
    let canonical = (0..n)
        .map(|i| format!("(vec-get sh {i})"))
        .collect::<Vec<_>>();
    let key = op.node(&format!("_shape_{name}"), &canonical, &kids, &pays);
    let shape_outputs = (0..=n)
        .map(|i| format!("(vec-get sh {i})"))
        .collect::<Vec<_>>()
        .join(" ");
    out.push(format!("(rule ((= c {node}) {group_facts} (= sh (node-shape (vec-of {}) (vec-of {})))) ((set {key} (values c (vec-get sh {n}))) (set {cached} (values {shape_outputs} (symmetries-of sh {})))) :ruleset slotted-shape)",edges.join(" "),groups.join(" "),n+1));
    out.push(format!("(rule ((= c {node}) {group_facts} (= (values {} back syms) {cached}) (= cs ({} c))) ((set ({} c) (group-restrict syms cs))) :ruleset slotted-group)",shapes.join(" "),s.free_vars,s.group));
    let other = names("n", n);
    let other_node = op.node(name, &other, &kids, &pays);
    let other_cached = cache(&other);
    out.push(format!("(rule ((= c {node}) {group_facts} (= (values {} b1 syms1) {cached}) (= c {other_node}) (= (values {} b2 syms2) {other_cached}) (= v1 (vec-of {})) (= v2 (vec-of {})) (!= v1 v2) (= v1 (ordering-max v1 v2))) ((delete {node})) :ruleset slotted-shape)",shapes.join(" "),shapes.join(" "),edges.join(" "),other.join(" ")));
    let node_cols = &node[name.len() + 2..node.len() - 1];
    for j in 0..n {
        if op.children()[j] == &Column::Binder {
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
        out.push(format!("(rule ((= row {node}) (= grp ({} {})) (= pinned (map-domain (compose {pinned} {})))) ((set (_pinned_{name} {node_cols} {}) pinned) (set ({} {} pinned) (group-coset-reps grp pinned))) :ruleset slotted-read)",s.group,kids[j],edges[j],j+1,s.coset_reps,kids[j]));
    }
    let moved = op.node(name, &other, &kids, &pays);
    let pulls = other
        .iter()
        .zip(&edges)
        .map(|(a, b)| format!("(= {a} (compose R {b}))"))
        .collect::<Vec<_>>()
        .join(" ");
    out.push(format!("(rule (({} e2 m e1) (= e2 {node}) (!= e1 e2) (= e2 (ordering-max e1 e2)) (= nodeslots {slots}) (= R (find-mapping-total (map-domain m) nodeslots (map-domain m) m)) {pulls}) ((union e1 {moved}) (delete {node})) :ruleset slotted-migrate)",s.renames));
    for pos in 0..n {
        let mut es = edges.clone();
        let mut ks = kids.clone();
        es[pos] = format!("(compose {} m)", edges[pos]);
        ks[pos] = "c'".into();
        let new = op.node(name, &es, &ks, &pays);
        let child = &kids[pos];
        let edge = &edges[pos];
        let bound = if op.children()[pos] == &Column::Binder {
            format!("(= bound{pos} (map-get {} 0))", es[pos])
        } else {
            String::new()
        };
        out.push(format!("(rule (({} {child} m c') (= node {node}) {bound} (= {child} (ordering-max {child} c')) (guard (or (bool-!= {child} c') (bool= (compose m m) m))) (guard (or (bool-!= {child} c') (bool-!= (compose {edge} m) {edge})))) ((union node {new}) (delete {node})) :ruleset slotted-migrate)",s.renames));
    }
    if let Some(covered) = op.covered() {
        let binders = op.binders();
        let mut es = edges.clone();
        let mut ks = kids.clone();
        for (i, &pos) in binders.iter().enumerate() {
            es[pos] = format!("mvar{i}");
            ks[pos] = format!("({} 0)", s.var);
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
                .map(|&u| format!("(map-not-contains (map-image {}) v{i})", edges[u]))
                .collect::<Vec<_>>()
                .join(" ");
            out.push(format!("(rule (({} {bound_node} ml l) (= v{i} (map-get mvar{i} 0)) {free}) (({} {bound_node} (inverse (map-remove (inverse ml) v{i})) l)))",s.renames,s.equated));
            for &u in &uncovered {
                let mut fresh = es.clone();
                fresh[pos] = format!("(map-of 0 w{i})");
                fresh[covered] = format!(
                    "(compose (map-insert (map-image {}) v{i} w{i}) {})",
                    edges[covered], edges[covered]
                );
                let renamed = op.node(name, &fresh, &ks, &pays);
                out.push(format!("(rule ((= node {bound_node}) (= v{i} (map-get mvar{i} 0)) (map-contains (map-image {}) v{i}) (= used {all_slots}) (= fresh{i} (find-mapping-total used (map-of 0 0) (map-empty) (map-empty))) (= w{i} (map-get fresh{i} 0))) ((union node {renamed}) (delete {bound_node})))",edges[u]));
            }
        }
    }
    machinery(&out.join("\n"))
}
