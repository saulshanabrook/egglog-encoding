//! Reference oracle for differential-testing the egglog slotted encoding's
//! multipattern matching against `slotted-egraphs`.
//!
//! Reads a spec on stdin and prints one `PARTITION <groups>` line: the probe
//! terms grouped by the e-graph's own equality after saturating the given rule.
//! The encoding side runs the same spec and the two lines are compared.
//!
//! Spec lines (`#` comments and blanks ignored):
//!
//! ```text
//! term   <sexpr>              add a term
//! union  <sexpr> <sexpr>      union two terms
//! rule                        start a new rule (the first `atom` opens one)
//! atom   <root> <op> <c>...      one depth-1 multipattern atom (pvar names)
//! cond   in|notin $<slot> <pvar>...   side condition on the match
//! action <root> <op> <a> <b>  union ?root with (op ?a ?b)
//! rhs    <root> <pattern>    union ?root with a nested right-hand side
//! nested <pattern>           run this rule through the single-pattern matcher;
//!                            its `cond` lines still apply
//! probe  <sexpr>              term to include in the reported partition
//! rounds <n>                  saturation rounds (default 10)
//! ```
//!
//! Two limits of that language, both about payload leaves:
//!
//! * an `atom` child starting with `$` is a slot, one starting with `#` is a PAYLOAD
//!   literal, and anything else becomes a *pattern variable* -- so `atom p add e 0` is
//!   `?p == (add ?e ?0)` and matches any second child, where `atom p add e #0` asks for
//!   the literal. The child count is free: the atoms are handed to
//!   `MultiPattern::parse`, which takes any arity.
//! * a leaf needs an atom of its own, since an atom's child has to be a pattern
//!   variable: `atom c sym:mult` then `atom p binop c a b`.
//! * On that path a payload leaf is only a payload if its spelling is not also an
//!   operator tag. `from_syntax` matches the tags first, so `add` and `sub` are
//!   the array language's binary nodes here (and fail to parse, having no
//!   children), while `null` would silently parse as the `Null` node instead of
//!   `Symbol("null")`. A generator that needs payload symbols should spell them
//!   so they cannot collide; `xdiff/xsdql.py` prefixes every one.

use slotted_egraphs::*;
use std::collections::BTreeSet;
use std::io::Read;

define_language! {
    pub enum L {
        Var(Slot) = "var",
        Null() = "null",
        // The machinery encodes this as `(App "lambda" {0->x} (Var 0) mb body)`,
        // so the bound slot rides in the first child's edge on that side.
        Lam(Bind<AppliedId>) = "lam",
        F(AppliedId, AppliedId) = "f",
        G(AppliedId, AppliedId) = "g",
        H(AppliedId, AppliedId) = "h",
        K(AppliedId, AppliedId) = "k",
        Sub(AppliedId, AppliedId) = "sub",
        Sub2(AppliedId, AppliedId) = "sub2",
        Add(AppliedId, AppliedId) = "add",
        // The paper's S4.1 array language (Listing 1). `Lam` and `Var` above are
        // already its binder and its variable; these are the rest. The paper
        // writes `Let(RenamedId, Bind<RenamedId>)`, i.e. `(let ?e $x ?body)`;
        // this is the same constructor with its columns in the order the
        // reference's own `tests/rise` and `tests/array` use, `(let $x ?body ?e)`,
        // which is also the order the encoding's `App3 "let"` has.
        App(AppliedId, AppliedId) = "app",
        Let(Bind<AppliedId>, AppliedId) = "let",
        Number(u32),
        Symbol(Symbol),

        // The `sdql` language, `slotted-egraphs/benches/sdql.rs` column for
        // column. `define_language!` dispatches parsing on the operator string
        // alone -- the generated `from_syntax` is a `match` on it -- so a tag
        // may appear once in the enum, and a variant name once. Where the toy
        // and array languages above already took one, the *variant* is renamed
        // and the reference's tag kept, since only the tag is what rule and
        // term text says:
        //
        //     Lam    -> Lambda    Add -> Plus    Sub -> Minus    App -> Apply
        //
        // `Var(Slot) = "var"`, `Number(u32)` and `Symbol(Symbol)` are shared
        // outright: `sdql`'s are the same three constructors.
        //
        // `Let` is the one that could not keep its tag. `sdql`'s is
        // `Let(AppliedId, Bind<AppliedId>)`, i.e. `(let ?v $x ?body)`, while
        // "let" above is `Let(Bind<AppliedId>, AppliedId)`, i.e.
        // `(let $x ?body ?v)` -- the same information in another column order,
        // but a *different* node. Two arms for one tag would leave the second
        // unreachable and parse `sdql`'s `let` as the array one, so this one is
        // tagged "sdql-let" and the harness writes that.
        Lambda(Bind<AppliedId>) = "lambda",
        Sing(AppliedId, AppliedId) = "sing",
        Plus(AppliedId, AppliedId) = "+",
        Mult(AppliedId, AppliedId) = "*",
        Minus(AppliedId, AppliedId) = "-",
        Equality(AppliedId, AppliedId) = "eq",
        Get(AppliedId, AppliedId) = "get",
        Range(AppliedId, AppliedId) = "range",
        Apply(AppliedId, AppliedId) = "apply",
        IfThen(AppliedId, AppliedId) = "ifthen",
        Binop(AppliedId, AppliedId, AppliedId) = "binop",
        SubArray(AppliedId, AppliedId, AppliedId) = "subarray",
        Unique(AppliedId) = "unique",
        Sum(
            /*  range: */ AppliedId,
            /*   body: */ Bind<Bind<AppliedId>>,
        ) = "sum",
        Merge(
            /* range1: */ AppliedId,
            /* range2: */ AppliedId,
            /*   body: */ Bind<Bind<Bind<AppliedId>>>,
        ) = "merge",
        SdqlLet(
            /*      v: */ AppliedId,
            /*   body: */ Bind<AppliedId>,
        ) = "sdql-let",
    }
}

type G = EGraph<L>;

/// A side condition on a match: is the slot among the variable's slots?
///
/// `want` says whether the slot should appear in the slots of *any* listed
/// variable, which covers the reference's conditions: `$1 not in slots(?b)`,
/// `$1 in slots(?b)`, and `let-app`'s `$1 in slots(?a) or $1 in slots(?b)`.
#[derive(Clone)]
struct Cond {
    slot: Slot,
    pvars: Vec<String>,
    want: bool,
}

/// One rewrite: a multipattern, side conditions, and what to do with each match.
#[derive(Default)]
struct RuleSpec {
    atoms: Vec<String>,
    conds: Vec<Cond>,
    action: Option<(String, String, String, String)>,
    /// `(root, pattern)` for a right-hand side that is not depth-1. The reference's
    /// pattern parser handles nesting, so this only has to be handed over as text.
    rhs: Option<(String, String)>,
    /// The same rule as one *nested* pattern, run through the single-pattern
    /// matcher instead of `multi_ematch`. The two are not equivalent: the depth-1
    /// matcher sees through redundant slots that `ematch_all` does not, so it proves
    /// at least as much and sometimes more. This is how the difference is measured.
    nested_lhs: Option<String>,
}

struct Spec {
    /// Print a structured dump of every class and node after saturating, so the two
    /// sides can be compared on more than the probe partition.
    dump: bool,
    terms: Vec<String>,
    unions: Vec<(String, String)>,
    /// A `rule` line starts a new one; with none, the first `atom` opens one, so a
    /// single-rule spec needs no separator.
    rules: Vec<RuleSpec>,
    probes: Vec<String>,
    rounds: usize,
}

fn parse_spec(src: &str) -> Spec {
    let mut s = Spec {
        dump: false,
        terms: vec![],
        unions: vec![],
        rules: vec![],
        probes: vec![],
        rounds: 10,
    };
    for line in src.lines() {
        let line = line.trim();
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        let (kind, rest) = line.split_once(char::is_whitespace).unwrap_or((line, ""));
        let rest = rest.trim();
        match kind {
            "dump" => s.dump = true,
            "term" => s.terms.push(rest.to_string()),
            "probe" => s.probes.push(rest.to_string()),
            "rounds" => s.rounds = rest.parse().unwrap(),
            "union" => {
                let (a, b) = split_two_sexprs(rest);
                s.unions.push((a, b));
            }
            // `?p == (op ?c1 ?c2)` is rebuilt from the four names, so the
            // generator does not have to agree on pattern syntax.
            // A child written `$v` is a slot literal and goes through as-is; a
            // binder's slot must be one, since `Bind` has no room for a pattern
            // variable there.
            "rule" => s.rules.push(RuleSpec::default()),
            // `cond in|notin $slot pvar...`
            "cond" => {
                let w: Vec<&str> = rest.split_whitespace().collect();
                let want = match w[0] {
                    "in" => true,
                    "notin" => false,
                    other => panic!("unknown cond kind: {other}"),
                };
                if s.rules.is_empty() {
                    s.rules.push(RuleSpec::default());
                }
                s.rules.last_mut().unwrap().conds.push(Cond {
                    slot: Slot::named(w[1].trim_start_matches('$')),
                    pvars: w[2..].iter().map(|v| v.to_string()).collect(),
                    want,
                });
            }
            "atom" => {
                let w: Vec<&str> = rest.split_whitespace().collect();
                let kid = |c: &str| {
                    if let Some(payload) = c.strip_prefix('#') {
                        // a payload literal, not a pattern variable
                        payload.to_string()
                    } else if c.starts_with('$') {
                        c.to_string()
                    } else {
                        format!("?{c}")
                    }
                };
                if s.rules.is_empty() {
                    s.rules.push(RuleSpec::default());
                }
                let kids: Vec<String> = w[2..].iter().map(|c| kid(c)).collect();
                s.rules.last_mut().unwrap().atoms.push(format!(
                    "?{} == ({} {})",
                    w[0],
                    w[1],
                    kids.join(" ")
                ));
            }
            // `nested <pattern>` runs the rule through the single-pattern matcher
            "nested" => {
                if s.rules.is_empty() {
                    s.rules.push(RuleSpec::default());
                }
                s.rules.last_mut().unwrap().nested_lhs = Some(rest.to_string());
            }
            // `rhs <root> <pattern>`, e.g. `rhs p (h (g ?a ?b) ?b)`
            "rhs" => {
                let (root, pat) = rest.split_once(char::is_whitespace).unwrap();
                if s.rules.is_empty() {
                    s.rules.push(RuleSpec::default());
                }
                s.rules.last_mut().unwrap().rhs =
                    Some((root.to_string(), pat.trim().to_string()));
            }
            "action" => {
                let w: Vec<&str> = rest.split_whitespace().collect();
                if s.rules.is_empty() {
                    s.rules.push(RuleSpec::default());
                }
                s.rules.last_mut().unwrap().action = Some((
                    w[0].to_string(),
                    w[1].to_string(),
                    w[2].to_string(),
                    w[3].to_string(),
                ));
            }
            other => panic!("unknown spec line kind: {other}"),
        }
    }
    s
}

/// Split `"<sexpr> <sexpr>"` at the top-level boundary between the two.
fn split_two_sexprs(s: &str) -> (String, String) {
    let mut depth = 0i32;
    for (i, ch) in s.char_indices() {
        match ch {
            '(' => depth += 1,
            ')' => {
                depth -= 1;
                if depth == 0 {
                    return (s[..=i].trim().to_string(), s[i + 1..].trim().to_string());
                }
            }
            ' ' if depth == 0 && i > 0 => {
                return (s[..i].trim().to_string(), s[i + 1..].trim().to_string());
            }
            _ => {}
        }
    }
    panic!("cannot split two s-exprs from {s:?}");
}

/// Does the match satisfy the condition?
fn holds(c: &Cond, subst: &Subst) -> bool {
    let found = c
        .pvars
        .iter()
        .any(|v| subst.get(v).is_some_and(|a| a.slots().contains(&c.slot)));
    found == c.want
}

fn add(eg: &mut G, s: &str) -> AppliedId {
    eg.add_expr(RecExpr::<L>::parse(s).unwrap())
}

fn main() {
    let mut src = String::new();
    std::io::stdin().read_to_string(&mut src).unwrap();
    let spec = parse_spec(&src);

    let mut eg = G::default();
    for t in &spec.terms {
        add(&mut eg, t);
    }
    for (a, b) in &spec.unions {
        let x = add(&mut eg, a);
        let y = add(&mut eg, b);
        eg.union(&x, &y);
    }
    for p in &spec.probes {
        add(&mut eg, p);
    }

    // Every rule with both a pattern and an action, compiled once.
    let compiled: Vec<(usize, MultiPattern<L>, Pattern<L>, Pattern<L>)> = spec
        .rules
        .iter()
        .enumerate()
        .filter_map(|(i, r)| {
            if r.atoms.is_empty() || r.nested_lhs.is_some() {
                return None;
            }
            let pat = MultiPattern::parse(&r.atoms.join(", ")).unwrap();
            if let Some((root, text)) = &r.rhs {
                let from = Pattern::PVar(root.clone());
                let to = Pattern::parse(text).unwrap();
                return Some((i, pat, from, to));
            }
            let (root, op, a, b) = r.action.as_ref()?;
            let from = Pattern::PVar(root.clone());
            // `action <root> = <x> <x>` equates two pattern variables directly, so
            // both sides can carry a non-identity renaming. Anything else builds a
            // node, which is always at the identity in pattern slots.
            let to: Pattern<L> = if op == "=" {
                Pattern::PVar(a.clone())
            } else {
                Pattern::parse(&format!("({op} ?{a} ?{b})")).unwrap()
            };
            Some((i, pat, from, to))
        })
        .collect();

    // Rules given in nested form go through the single-pattern matcher. A spec uses
    // one form or the other, never both, so the two loops do not interact.
    let nested: Vec<Rewrite<L>> = spec
        .rules
        .iter()
        .filter_map(|r| {
            let lhs = r.nested_lhs.as_ref()?;
            let (_, text) = r.rhs.as_ref()?;
            // A nested rule's `cond` lines have to be applied here too. They used
            // not to be, so a conditional rule written in nested form compared the
            // encoding's guarded rule against an *unguarded* reference, and the
            // reference fired where the rule says it must not.
            let conds = r.conds.clone();
            Some(Rewrite::new_if("r", lhs, text, move |subst, _| {
                conds.iter().all(|c| holds(c, subst))
            }))
        })
        .collect();
    if !nested.is_empty() {
        let mut saturated = false;
        for _ in 0..spec.rounds {
            if !apply_rewrites(&mut eg, &nested) {
                saturated = true;
                break;
            }
        }
        println!("SATURATED {}", if saturated { "yes" } else { "no" });
    }

    if !compiled.is_empty() {
        let debug = std::env::var("XMULTI_DEBUG").is_ok();
        let mut saturated = false;
        for round in 0..spec.rounds {
            let before = eg.progress();
            // Match every rule against the same e-graph, then apply: a rule set is
            // one step of all rules, not a sequence of separate runs.
            let found: Vec<(usize, Vec<Subst>)> = compiled
                .iter()
                .enumerate()
                .map(|(i, (_, pat, _, _))| (i, multi_ematch(pat, &eg)))
                .collect();
            if debug {
                for (i, substs) in &found {
                    eprintln!("round {round} rule {i}: {} match(es)", substs.len());
                }
            }
            for (i, substs) in found {
                let (ri, _, from, to) = &compiled[i];
                let conds = &spec.rules[*ri].conds;
                for s in substs {
                    // A side condition asks about the *slots* of what a variable
                    // matched, which is why it cannot be a pattern: it is a property
                    // of the match, not of the shape.
                    if !conds.iter().all(|c| holds(c, &s)) {
                        continue;
                    }
                    eg.union_instantiations(from, to, &s, None);
                }
            }
            if before == eg.progress() {
                saturated = true;
                break;
            }
        }
        // A case that hit the round cap without settling means the two sides ran
        // different amounts of work, so comparing them says nothing.
        println!("SATURATED {}", if saturated { "yes" } else { "no" });
    }

    if spec.dump {
        dump_structured(&eg);
    }
    println!("PARTITION {}", partition(&eg, &spec.probes));
}

/// A class's symmetry group, as every permutation of its slots that it proves.
///
/// The group is not part of the node set: a commutative class holds *one* node and a
/// swap, where a class without the swap holds the same one node. So a comparison that
/// looks only at nodes cannot tell them apart, and this is the missing half.
///
/// `group` itself is crate-private, but `eq` on two AppliedIds over the same class is
/// exactly a membership test on `a.m * b.m^-1`, so enumerating permutations recovers it.
/// A class with more slots than `SLOT_CAP` is reported as `?` rather than silently
/// skipped, since 6! is where this stops being cheap.
fn group_of(eg: &G, id: Id) -> Vec<String> {
    const SLOT_CAP: usize = 6;
    let mut slots: Vec<Slot> = eg.slots(id).iter().copied().collect();
    slots.sort_by_key(|s| s.to_string());
    if slots.len() > SLOT_CAP {
        return vec!["?".to_string()];
    }
    let ident = SlotMap::identity(&slots.iter().copied().collect());
    let mut out = Vec::new();
    for perm in permutations(&slots) {
        let mut m = SlotMap::new();
        for (a, b) in slots.iter().zip(&perm) {
            m.insert(*a, *b);
        }
        let x = AppliedId::new(id, ident.clone());
        let y = AppliedId::new(id, m.clone());
        if eg.eq(&x, &y) {
            let mut parts: Vec<String> = slots
                .iter()
                .zip(&perm)
                .map(|(a, b)| format!("{a}>{b}"))
                .collect();
            parts.sort();
            out.push(parts.join("|"));
        }
    }
    out.sort();
    out
}

fn permutations(xs: &[Slot]) -> Vec<Vec<Slot>> {
    if xs.is_empty() {
        return vec![vec![]];
    }
    let mut out = Vec::new();
    for i in 0..xs.len() {
        let mut rest = xs.to_vec();
        let head = rest.remove(i);
        for mut p in permutations(&rest) {
            p.insert(0, head);
            out.push(p);
        }
    }
    out
}

/// Every class and node, in a form the encoding side can be compared against.
///
/// `to_syntax` gives a node as a sequence of operator/payload strings, child
/// invocations and slot literals, so nothing has to be recovered from `Debug`
/// output. Slot *names* are printed as they are; the comparison is what
/// canonicalises them away, since the two sides pick names independently.
fn dump_structured(eg: &G) {
    let mut ids = eg.ids();
    ids.sort_by_key(|i| format!("{i:?}"));
    for id in ids {
        let mut slots: Vec<String> = eg.slots(id).iter().map(|s| s.to_string()).collect();
        slots.sort();
        println!("CLASS {:?} SLOTS {}", id, slots.join(","));
        println!("GROUP {:?} {}", id, group_of(eg, id).join(";"));
        let mut lines: Vec<String> = Vec::new();
        for node in eg.enodes(id) {
            let mut parts: Vec<String> = Vec::new();
            for e in node.to_syntax() {
                match e {
                    SyntaxElem::String(t) => parts.push(format!("o:{t}")),
                    SyntaxElem::Slot(s) => parts.push(format!("s:{s}")),
                    SyntaxElem::AppliedId(a) => {
                        let mut m: Vec<String> = a
                            .m
                            .iter()
                            .map(|(k, v)| format!("{k}>{v}"))
                            .collect();
                        m.sort();
                        parts.push(format!("c:{:?}:{}", eg.find_applied_id(&a).id, m.join("|")));
                    }
                }
            }
            lines.push(format!("NODE {:?} {}", id, parts.join(" ")));
        }
        lines.sort();
        for l in lines {
            println!("{l}");
        }
    }
}

/// Probe indices grouped by **e-class identity**, as a canonical string.
///
/// Deliberately not `eg.eq`, which is equality of *renamed ids* and so depends
/// on which slot names the invocation carries: after a redundancy two probe
/// terms can sit in one e-class while naming different surviving slots, and
/// `eg.eq` calls those unequal. The encoding side reads e-class identity out of
/// egglog, so this is the notion that makes the two comparable.
fn partition(eg: &G, probes: &[String]) -> String {
    let ids: Vec<Option<AppliedId>> = probes
        .iter()
        .map(|p| lookup_rec_expr(&RecExpr::<L>::parse(p).unwrap(), eg))
        .collect();

    let mut groups: Vec<BTreeSet<usize>> = Vec::new();
    let mut missing: Vec<usize> = Vec::new();
    for i in 0..probes.len() {
        let Some(a) = &ids[i] else {
            missing.push(i);
            continue;
        };
        let mut placed = false;
        for g in groups.iter_mut() {
            let j = *g.iter().next().unwrap();
            let b = ids[j].as_ref().unwrap();
            if eg.find_applied_id(a).id == eg.find_applied_id(b).id {
                g.insert(i);
                placed = true;
                break;
            }
        }
        if !placed {
            groups.push([i].into_iter().collect());
        }
    }
    let mut gs: Vec<String> = groups
        .iter()
        .map(|g| {
            let v: Vec<String> = g.iter().map(|i| i.to_string()).collect();
            format!("[{}]", v.join(","))
        })
        .collect();
    gs.sort();
    format!("{} missing[{:?}]", gs.join(""), missing)
}
