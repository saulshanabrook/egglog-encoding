use super::model::*;
use super::query::{self, Atom, Conditions, Query, names_expr};
use super::syntax::quote;

enum Slots {
    Name(String),
    Set(String),
}
struct Built {
    edge: String,
    value: String,
    slots: Slots,
}

fn build(
    lang: &Language,
    t: &Term,
    sort: &str,
    q: &mut Query,
    actions: &mut Vec<String>,
    root: bool,
) -> Result<Built, String> {
    match t {
        Term::Variable(pv) => {
            let value = q.class(pv)?;
            if q.sorts[pv] != sort {
                return Err(format!(
                    "right-hand side uses {pv} at the wrong carrier sort"
                ));
            }
            Ok(Built {
                edge: q.maps[pv].clone(),
                value,
                slots: Slots::Name(pv.clone()),
            })
        }
        Term::Slot(s) => Ok(Built {
            edge: format!("(ren {} {})", q.frame, quote(s)),
            value: format!("({} 0)", lang.symbols(sort).var),
            slots: Slots::Name(s.clone()),
        }),
        Term::Node(n, args) => {
            let op = &lang.constructors[n];
            if op.sort != sort {
                return Err(format!("{n} produces {}, expected {sort}", op.sort));
            }
            let (children, pays) = op.split(args);
            let pays = pays
                .into_iter()
                .map(|p| q.payload(p))
                .collect::<Result<Vec<_>, _>>()?;
            if children.is_empty() {
                let node = op.node(n, &[], &[], &pays);
                let value = if t.has_payload_variable() {
                    let v = q.fresh(&format!("built_{}", n.to_lowercase()));
                    actions.push(format!("(let {v} {node})"));
                    v
                } else {
                    node
                };
                return Ok(Built {
                    edge: "(map-empty)".into(),
                    value,
                    slots: Slots::Set("(map-empty)".into()),
                });
            }
            let mut built = Vec::new();
            for c in &children {
                built.push(build(lang, c, sort, q, actions, false)?);
            }
            let value = q.fresh(&format!("built_{}", n.to_lowercase()));
            let mut edges = built.iter().map(|b| b.edge.clone()).collect::<Vec<_>>();
            let back = if root {
                None
            } else {
                let sh = q.fresh(&format!("shape_{}", n.to_lowercase()));
                actions.push(format!("(let {sh} (shape {}))", edges.join(" ")));
                let back = format!("(vec-get {sh} {})", edges.len());
                edges = (0..edges.len())
                    .map(|i| format!("(vec-get {sh} {i})"))
                    .collect();
                Some(back)
            };
            let node = op.node(
                n,
                &edges,
                &built.iter().map(|b| b.value.clone()).collect::<Vec<_>>(),
                &pays,
            );
            actions.push(format!("(let {value} {node})"));
            let binders = op.binders();
            let bound = binders
                .iter()
                .map(|&i| match children[i] {
                    Term::Slot(s) => Ok(s.clone()),
                    _ => Err("a binder requires a slot literal".to_owned()),
                })
                .collect::<Result<Vec<_>, _>>()?;
            let (mut uncovered, mut covered, mut nested) = (Vec::new(), Vec::new(), Vec::new());
            for (i, b) in built.into_iter().enumerate() {
                let inside = binders.contains(&i) || Some(i) == op.covered();
                match b.slots {
                    Slots::Name(n) => {
                        if inside {
                            covered.push(n)
                        } else {
                            uncovered.push(n)
                        }
                    }
                    Slots::Set(s) => nested.push(if inside && !bound.is_empty() {
                        format!("(without {} {s} {})", q.frame, names_expr(bound.clone()))
                    } else {
                        s
                    }),
                }
            }
            let mut slots = format!(
                "(node-slots {} {} {} {})",
                q.frame,
                names_expr(uncovered),
                names_expr(covered),
                names_expr(bound)
            );
            for s in nested {
                slots = format!("(map-union {slots} {s})");
            }
            let sv = q.fresh(&format!("{value}_slots"));
            actions.push(format!("(let {sv} {slots})"));
            let edge = if let Some(back) = back {
                let ev = q.fresh(&format!("{value}_edge"));
                actions.push(format!("(let {ev} (compose {sv} {back}))"));
                ev
            } else {
                sv.clone()
            };
            Ok(Built {
                edge,
                value,
                slots: Slots::Set(sv),
            })
        }
        _ => Err("substitution must be the complete right-hand side".into()),
    }
}

fn substitute(
    lang: &Language,
    root: &str,
    args: &[Term; 3],
    q: &mut Query,
) -> Result<Vec<String>, String> {
    let [
        Term::Variable(body),
        Term::Slot(slot),
        Term::Variable(replacement),
    ] = args
    else {
        return Err(
            "subst requires a bound body variable, a slot, and a bound replacement variable".into(),
        );
    };
    let bc = q.class(body)?;
    let tc = q.class(replacement)?;
    let rc = q.class(root)?;
    let sort = &q.sorts[root];
    if &q.sorts[body] != sort || &q.sorts[replacement] != sort {
        return Err("subst arguments have different carrier sorts".into());
    }
    let s = lang.symbols(sort);
    let bm = q.maps[body].clone();
    let tm = q.maps[replacement].clone();
    let rm = q.maps[root].clone();
    let x = q
        .slots
        .get(slot)
        .ok_or_else(|| format!("unbound substitution slot {slot}"))?
        .clone();
    let (needed, into, bx, tr, back) = (
        q.fresh("needed"),
        q.fresh("into_body"),
        q.fresh("body_x"),
        q.fresh("t_ren"),
        q.fresh("back"),
    );
    let inputs = format!("{bc} {bx} ({} 0) {tr} {tc} {}", s.var, quote(&s.free_vars));
    Ok(vec![
        format!(
            "(let {needed} (map-union (map-image {bm}) (map-union (map-image {tm}) (map-of {x} {x}))))"
        ),
        format!(
            "(let {into} (find-mapping-total (map-domain {bm}) {needed} (map-domain {bm}) {bm}))"
        ),
        format!("(let {bx} (map-get {into} {x}))"),
        format!("(let {tr} (compose-total {into} {tm}))"),
        format!("(let {back} (compose (inverse {rm}) (inverse {into})))"),
        format!(
            "({} {rc} {back} (slotted-subst-frame {inputs}) (slotted-subst {inputs}))",
            s.subst_pending
        ),
    ])
}

fn rule(
    body: &[String],
    actions: &[String],
    naive: bool,
    ruleset: Option<&str>,
    name: Option<&str>,
) -> String {
    let mut options = String::new();
    if naive {
        options.push_str(" :naive");
    }
    if let Some(rs) = ruleset {
        options.push_str(&format!(" :ruleset {rs}"));
    }
    if let Some(n) = name {
        options.push_str(&format!(" :name {}", quote(n)));
    }
    format!(
        "(rule ({}) ({}){options})",
        body.join("\n "),
        actions.join("\n ")
    )
}

pub(super) struct Rewrite<'a> {
    pub root: &'a str,
    pub atoms: &'a [Atom],
    pub rhs: &'a Term,
    pub conditions: Conditions,
    pub name: Option<&'a str>,
    pub ordinal: usize,
    pub nested: bool,
}

pub(super) fn compile(lang: &Language, mut r: Rewrite<'_>) -> Result<String, String> {
    let mut rhs = r.rhs.clone();
    lang.refresh_shadowed(&mut rhs);
    let mut fresh = std::collections::BTreeSet::new();
    rhs.slot_literals(&mut fresh);
    for a in r.atoms {
        for k in &a.kids {
            if let Term::Slot(s) = k {
                fresh.remove(s);
            }
        }
    }
    r.conditions.fresh.extend(fresh);
    let mut q = query::compile(
        lang,
        r.atoms,
        &r.conditions,
        "",
        true,
        Some(r.root),
        r.nested,
    )?;
    let root_sort = q.sorts[r.root].clone();
    let root_class = q.class(r.root)?;
    let sy = lang.symbols(&root_sort);
    let actions = match &rhs {
        Term::Variable(pv) => {
            let c = q.class(pv)?;
            if q.sorts[pv] != root_sort {
                return Err("a rewrite's result has a different carrier sort".into());
            }
            vec![format!(
                "({} {root_class} (compose (inverse {}) {}) {c})",
                sy.equated, q.maps[r.root], q.maps[pv]
            )]
        }
        Term::Subst(args) => substitute(lang, r.root, args, &mut q)?,
        _ => {
            let mut acts = Vec::new();
            let node = build(lang, &rhs, &root_sort, &mut q, &mut acts, true)?;
            acts.push(format!("(union {} {root_class})", node.value));
            acts
        }
    };
    let naive = rhs.uses_subst();
    let Some(split) = q.split else {
        return Ok(rule(&q.body, &actions, naive, None, r.name));
    };
    let relation = format!("_slotted_match_{}", r.ordinal);
    let mut columns = vec![q.refined.clone(), q.length.clone()];
    let mut sorts = vec!["Frames".to_owned(), "i64".to_owned()];
    for (pv, c) in &q.classes {
        columns.push(c.clone());
        sorts.push(q.sorts[pv].clone());
    }
    let mut pays = q.pays.values().collect::<Vec<_>>();
    pays.sort();
    for (v, s) in pays {
        columns.push(v.clone());
        sorts.push(s.clone());
    }
    let row = call(&relation, columns);
    let mut apply_body = vec![row.clone()];
    apply_body.extend_from_slice(&q.body[split..]);
    Ok([
        format!("(relation {relation} ({}))", sorts.join(" ")),
        rule(
            &q.body[..split],
            &[row.clone(), format!("(Idx {} 0)", q.length)],
            naive,
            None,
            r.name,
        ),
        rule(
            &apply_body,
            &actions,
            naive,
            Some("slotted-apply"),
            r.name.map(|n| format!("{n}/apply")).as_deref(),
        ),
        rule(
            std::slice::from_ref(&row),
            &[format!("(delete {row})")],
            false,
            Some("slotted-apply"),
            r.name.map(|n| format!("{n}/drain")).as_deref(),
        ),
    ]
    .join("\n"))
}
