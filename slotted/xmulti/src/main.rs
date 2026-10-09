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
//! goal   <sexpr>              test whether a term is equivalent to the first `term`
//! rounds <n>                  rounds to run, each applying every rule once (default 10)
//! sizes                       print live class/node counts without a graph dump
//! ```
//!
//! Two limits of that language, both about payload leaves:
//!
//! * an `atom` child starting with `$` is a slot, one starting with `#` is a PAYLOAD
//!   literal, and anything else becomes a *pattern variable* -- so `atom p add e 0` is
//!   `?p == (add ?e ?0)` and matches any second child, where `atom p add e #0` asks for
//!   the literal. The child count is free: the atoms are handed to
//!   `MultiPattern::parse`, which takes any arity. A binder column holds the bare
//!   `$x` that `Bind` holds, a rigid pattern slot; the compiler refuses a pattern
//!   variable there, so no other spelling reaches this binary.
//! * a leaf needs an atom of its own, since an atom's child has to be a pattern
//!   variable: `atom c sym:mult` then `atom p binop c a b`.
//! * On that path a payload leaf is only a payload if its spelling is not also an
//!   operator tag. `from_syntax` matches the tags first, so `add` and `sub` are
//!   the array language's binary nodes here (and fail to parse, having no
//!   children), while `null` would silently parse as the `Null` node instead of
//!   `Symbol("null")`. A generator that needs payload symbols should spell them
//!   so they cannot collide; `xdiff/xsdql.py` prefixes every one.

use num_bigint::BigUint;
use slotted_egraphs::*;
use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet, HashMap};
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

const GROUP_SLOT_CAP: usize = 6;

/// The cap, or what `XMULTI_GROUP_SLOT_CAP` raises it to for a one-off dump of a
/// graph with wider classes; enumerating a class's symmetries costs its width's
/// factorial `eq` tests, so ten is already seconds per class.
fn group_slot_cap() -> usize {
    std::env::var("XMULTI_GROUP_SLOT_CAP")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(GROUP_SLOT_CAP)
}

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
    sizes: bool,
    terms: Vec<String>,
    unions: Vec<(String, String)>,
    /// A `rule` line starts a new one; with none, the first `atom` opens one, so a
    /// single-rule spec needs no separator.
    rules: Vec<RuleSpec>,
    probes: Vec<String>,
    goals: Vec<String>,
    rounds: usize,
    /// `ctor <tag> <Name>`: what the encoding calls the constructor behind a tag, for
    /// the substitution snapshot's tie-break (`symbol` and `number` name the payload
    /// leaves). Without it a variant's own name stands in.
    ctors: HashMap<String, String>,
}

fn parse_spec(src: &str) -> Spec {
    let mut s = Spec {
        dump: false,
        sizes: false,
        terms: vec![],
        unions: vec![],
        rules: vec![],
        probes: vec![],
        goals: vec![],
        rounds: 10,
        ctors: HashMap::new(),
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
            "sizes" => s.sizes = true,
            "term" => s.terms.push(rest.to_string()),
            "ctor" => {
                let (tag, name) = rest
                    .split_once(char::is_whitespace)
                    .expect("ctor <tag> <Name>");
                s.ctors.insert(tag.to_string(), name.trim().to_string());
            }
            "probe" => s.probes.push(rest.to_string()),
            "goal" => s.goals.push(rest.to_string()),
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
                s.rules.last_mut().unwrap().rhs = Some((root.to_string(), pat.trim().to_string()));
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

// ------------------------------------------------------------ substitution snapshot
//
// The encoding computes every substitution of a round from the e-graph as the round
// began (its `beta/apply` rule runs in one apply phase, whose reads are the phase's
// snapshot), into the smallest term of the body's class, ties broken by a canonical
// spelling of the term (`sort/slotted/subst.rs`, `cheapest`). The crate's substitution
// methods read the e-graph at application time, after the round's earlier unions,
// and its syntactic method takes the node a class was created with -- history the
// encoding cannot replay. `SnapshotSubst` does what the encoding does, so that the
// two sides build the same terms and the final graphs can be the same.

thread_local! {
    static SNAPSHOT: RefCell<Option<Snapshot>> = const { RefCell::new(None) };
    static CTORS: RefCell<HashMap<String, String>> = RefCell::new(HashMap::new());
}

/// One piece of a term's spelling, as `sort/slotted/subst.rs` spells it.
#[derive(Clone, Debug, PartialEq, Eq)]
enum Tok {
    Text(String),
    /// a slot of the class, by its name there; a parent carries it through its edge
    Public(Slot),
    /// a slot internal to the term -- bound, or private to one node
    Inner(usize),
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum InnerKey {
    Bound(Slot),
    Private(Slot),
    ChildInner(usize, usize),
}

/// The chosen node per class, in the class's own slot names.
struct Snapshot {
    best: HashMap<Id, L>,
}

fn ast_size(node: &L, cost: &HashMap<Id, BigUint>) -> Option<BigUint> {
    node.applied_id_occurrences()
        .iter()
        .try_fold(BigUint::from(1u8), |total, child| {
            Some(total + cost.get(&child.id)?)
        })
}

/// What the encoding calls this node's constructor.
fn ctor_name(node: &L, syntax: &[SyntaxElem]) -> String {
    let tag = match node {
        L::Symbol(_) => "symbol".to_string(),
        L::Number(_) => "number".to_string(),
        _ => match &syntax[0] {
            SyntaxElem::String(tag) => tag.clone(),
            _ => panic!("a tagged node starts with its tag"),
        },
    };
    CTORS.with(|c| c.borrow().get(&tag).cloned().unwrap_or(tag))
}

/// A node's term, spelt from its children's templates, with slots classified in the
/// node's frame: a bound slot, a slot of the class, or one private to the node.
fn template(node: &L, public: &SmallHashSet<Slot>, templates: &HashMap<Id, Vec<Tok>>) -> Vec<Tok> {
    let syntax = node.to_syntax();
    let mut inner: BTreeMap<InnerKey, usize> = BTreeMap::new();
    let intern = |key: InnerKey, inner: &mut BTreeMap<InnerKey, usize>| {
        let next = inner.len();
        Tok::Inner(*inner.entry(key).or_insert(next))
    };
    let mut out = vec![
        Tok::Text(ctor_name(node, &syntax)),
        Tok::Text("(".to_owned()),
    ];
    let columns: Vec<&SyntaxElem> = match node {
        L::Symbol(_) | L::Number(_) => syntax.iter().collect(),
        _ => syntax.iter().skip(1).collect(),
    };
    // a slot the node names outright -- `var`'s -- is an occurrence like a child's;
    // the others are the node's binders
    let direct: BTreeSet<Slot> = node.public_slot_occurrences().into_iter().collect();
    let bound: BTreeSet<Slot> = columns
        .iter()
        .filter_map(|e| match e {
            SyntaxElem::Slot(s) if !direct.contains(s) => Some(*s),
            _ => None,
        })
        .collect();
    for (col, elem) in columns.iter().enumerate() {
        match elem {
            SyntaxElem::Slot(s) if direct.contains(s) => {
                out.push(if public.contains(s) {
                    Tok::Public(*s)
                } else {
                    intern(InnerKey::Private(*s), &mut inner)
                });
            }
            SyntaxElem::Slot(s) => {
                out.push(Tok::Text("bind".to_owned()));
                out.push(intern(InnerKey::Bound(*s), &mut inner));
            }
            SyntaxElem::AppliedId(child) => {
                let tpl = templates
                    .get(&child.id)
                    .expect("a smallest node's children are spelt before it");
                for tok in tpl {
                    out.push(match tok {
                        Tok::Text(text) => Tok::Text(text.clone()),
                        Tok::Inner(j) => intern(InnerKey::ChildInner(col, *j), &mut inner),
                        Tok::Public(slot) => {
                            let name = child.m[*slot];
                            if bound.contains(&name) {
                                intern(InnerKey::Bound(name), &mut inner)
                            } else if public.contains(&name) {
                                Tok::Public(name)
                            } else {
                                intern(InnerKey::Private(name), &mut inner)
                            }
                        }
                    });
                }
            }
            SyntaxElem::String(payload) => out.push(Tok::Text(format!("{payload},"))),
        }
        if !matches!(elem, SyntaxElem::String(_)) {
            out.push(Tok::Text(",".to_owned()));
        }
    }
    out.push(Tok::Text(")".to_owned()));
    out
}

/// A template as text, every slot numbered by first occurrence.
fn spelling(template: &[Tok]) -> String {
    let mut public: BTreeMap<Slot, usize> = BTreeMap::new();
    let mut inner: BTreeMap<usize, usize> = BTreeMap::new();
    let mut out = String::new();
    for tok in template {
        match tok {
            Tok::Text(text) => out.push_str(text),
            Tok::Public(slot) => {
                let next = public.len();
                out.push_str(&format!("p{}", public.entry(*slot).or_insert(next)));
            }
            Tok::Inner(index) => {
                let next = inner.len();
                out.push_str(&format!("i{}", inner.entry(*index).or_insert(next)));
            }
        }
    }
    out
}

impl Snapshot {
    /// The smallest term of every class, as the e-graph stands now.
    fn take(eg: &G) {
        let ids = eg.ids();
        let nodes: HashMap<Id, Vec<L>> = ids
            .iter()
            .map(|id| {
                let mut ns: Vec<L> = eg.enodes(*id).into_iter().collect();
                ns.sort_by_key(|n| format!("{n:?}"));
                (*id, ns)
            })
            .collect();
        let mut cost: HashMap<Id, BigUint> = HashMap::new();
        loop {
            let mut changed = false;
            for id in &ids {
                for node in &nodes[id] {
                    let Some(total) = ast_size(node, &cost) else {
                        continue;
                    };
                    if cost.get(id).is_none_or(|prev| total < *prev) {
                        cost.insert(*id, total);
                        changed = true;
                    }
                }
            }
            if !changed {
                break;
            }
        }
        let mut by_size: Vec<(&BigUint, Id)> = cost.iter().map(|(id, c)| (c, *id)).collect();
        by_size.sort();
        let mut templates: HashMap<Id, Vec<Tok>> = HashMap::new();
        let mut best: HashMap<Id, L> = HashMap::new();
        for (class_size, id) in by_size {
            let public = eg.slots(id);
            let mut chosen: Option<(String, L, Vec<Tok>)> = None;
            for node in &nodes[&id] {
                if ast_size(node, &cost).as_ref() != Some(class_size) {
                    continue;
                }
                let tpl = template(node, &public, &templates);
                let key = spelling(&tpl);
                if chosen.as_ref().is_none_or(|(least, _, _)| key < *least) {
                    chosen = Some((key, node.clone(), tpl));
                }
            }
            let (_, node, tpl) = chosen.expect("a class with a size has a node of that size");
            best.insert(id, node);
            templates.insert(id, tpl);
        }
        SNAPSHOT.with(|s| *s.borrow_mut() = Some(Snapshot { best }));
    }

    /// The chosen term under an invocation, its private slots fresh.
    fn term(&self, i: &AppliedId) -> Option<RecExpr<L>> {
        let node = self.best.get(&i.id)?;
        // The invocation can name a slot that the stored node binds. Rename
        // bound occurrences first so applying its free-slot map cannot capture.
        let node = node.refresh_private().apply_slotmap_fresh(&i.m);
        let mut children = Vec::new();
        for child in node.applied_id_occurrences() {
            children.push(self.term(&child)?);
        }
        Some(RecExpr { node, children })
    }
}

/// `re[x := t]`, added node by node: the crate's own `do_term_subst`.
fn term_subst(eg: &mut G, re: &RecExpr<L>, x: &AppliedId, t: &AppliedId) -> AppliedId {
    let mut node = re.node.clone();
    let children: Vec<AppliedId> = re
        .children
        .iter()
        .map(|c| term_subst(eg, c, x, t))
        .collect();
    for (slot, child) in node.applied_id_occurrences_mut().into_iter().zip(children) {
        *slot = child;
    }
    let app_id = eg.add_syn(node);
    if app_id == *x {
        t.clone()
    } else {
        app_id
    }
}

struct SnapshotSubst;

impl SubstMethod<L, ()> for SnapshotSubst {
    fn new_boxed() -> Box<dyn SubstMethod<L, ()>> {
        Box::new(SnapshotSubst)
    }

    fn subst(&mut self, b: AppliedId, x: AppliedId, t: AppliedId, eg: &mut G) -> AppliedId {
        let term = SNAPSHOT.with(|s| s.borrow().as_ref().and_then(|snap| snap.term(&b)));
        match term {
            Some(term) => term_subst(eg, &term, &x, &t),
            // a class the round created, or no round yet: the crate's own choice
            None => SynExprSubst::new_boxed().subst(b, x, t, eg),
        }
    }
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

fn goal_reached(eg: &G, start: &AppliedId, goal: &str) -> bool {
    let found = lookup_rec_expr(&RecExpr::<L>::parse(goal).unwrap(), eg);
    // `XMULTI_DEBUG=1` says which of the two ways a goal fails: the term is not in the
    // graph at all, or it is there but in another class.
    if std::env::var("XMULTI_DEBUG").is_ok() {
        match &found {
            None => eprintln!("GOAL-LOOKUP none"),
            Some(f) => eprintln!("GOAL-LOOKUP {f:?} start {start:?} eq {}", eg.eq(start, f)),
        }
    }
    found.is_some_and(|found| eg.eq(start, &found))
}

fn main() {
    let mut src = String::new();
    std::io::stdin().read_to_string(&mut src).unwrap();
    let spec = parse_spec(&src);
    // Which build answered, so a timing log can tell a checked oracle from a plain one.
    println!(
        "CONFIG checks={}",
        if cfg!(feature = "checks") {
            "on"
        } else {
            "off"
        }
    );

    // Substitution: `snapshot` (the default) substitutes into the smallest term of
    // the class as the e-graph stood when the round began, ties broken by a canonical
    // spelling -- the encoding's own choice, made at the same moment, so the two build
    // the same terms. `XMULTI_SUBST=syntactic` is the crate's default, the node each
    // class was created with, read at application time; `extraction` the crate's
    // smallest-term method, also at application time.
    CTORS.with(|c| *c.borrow_mut() = spec.ctors.clone());
    let substitution = std::env::var("XMULTI_SUBST").unwrap_or_else(|_| "snapshot".to_owned());
    let mut eg = match substitution.as_str() {
        "syntactic" => G::default(),
        "extraction" => G::with_subst_method::<ExtractionSubst>(()),
        "snapshot" => G::with_subst_method::<SnapshotSubst>(()),
        _ => panic!("unknown XMULTI_SUBST: {substitution}"),
    };
    println!("CONFIG substitution={substitution}");
    let term_ids: Vec<AppliedId> = spec.terms.iter().map(|t| add(&mut eg, t)).collect();
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
        // `XMULTI_DEBUG=1` counts each nested rule's matches per round, the way the
        // multipattern loop below reports its own, so the two matchers and the
        // encoding can be compared on match counts.
        let debug_nested: Vec<(usize, Pattern<L>)> = if std::env::var("XMULTI_DEBUG").is_ok() {
            spec.rules
                .iter()
                .enumerate()
                .filter_map(|(i, r)| Some((i, Pattern::parse(r.nested_lhs.as_ref()?).ok()?)))
                .collect()
        } else {
            Vec::new()
        };
        for round in 0..spec.rounds {
            if substitution == "snapshot" {
                Snapshot::take(&eg);
            }
            for (i, pat) in &debug_nested {
                let found = ematch_all(&eg, pat);
                eprintln!("round {round} nested-rule {i}: {} match(es)", found.len());
                // `XMULTI_DEBUG_RULE=<i>` also prints that rule's substitutions.
                if std::env::var("XMULTI_DEBUG_RULE").ok().as_deref()
                    == Some(i.to_string().as_str())
                {
                    for subst in &found {
                        let mut entries: Vec<_> = subst.iter().collect();
                        entries.sort_by(|a, b| a.0.cmp(b.0));
                        eprintln!("  subst {entries:?}");
                    }
                }
            }
            if !apply_rewrites(&mut eg, &nested) {
                saturated = true;
                break;
            }
        }
        println!("SATURATED {}", if saturated { "yes" } else { "no" });
    }

    if !compiled.is_empty() {
        let debug = std::env::var("XMULTI_DEBUG").is_ok();
        let trace = std::env::var("XMULTI_TRACE").is_ok();
        let mut saturated = false;
        for round in 0..spec.rounds {
            if substitution == "snapshot" {
                Snapshot::take(&eg);
            }
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
                    // `XMULTI_TRACE=1` names every match applied, so a wrong union can be
                    // traced to the rule and substitution that made it.
                    if trace {
                        let mut names: Vec<&String> = s.keys().collect();
                        names.sort();
                        let shown: Vec<String> =
                            names.iter().map(|k| format!("?{k}={:?}", s[*k])).collect();
                        eprintln!("MATCH round={round} rule={i} {}", shown.join(" "));
                        // and the two terms the union equates, as the e-graph spells them,
                        // so a checker outside can decide whether they are really equal
                        let from_id = pattern_subst(&mut eg, from, &s);
                        let to_id = pattern_subst(&mut eg, to, &s);
                        // the printer can trip over a redundant slot; a union it cannot
                        // spell is still recorded, unspelt
                        let spell = |id: &AppliedId| {
                            std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                                re_to_pattern(&eg.get_syn_expr(id)).to_string()
                            }))
                            .unwrap_or_else(|_| "<unprintable>".to_string())
                        };
                        eprintln!(
                            "UNION round={round} rule={i} {} == {}",
                            spell(&from_id),
                            spell(&to_id)
                        );
                    }
                    eg.union_instantiations(from, to, &s, None);
                }
            }
            if before == eg.progress() {
                saturated = true;
                break;
            }
        }
        // Reported, not decisive. A generated rule set need not have a fixpoint, and a
        // round here applies every rule once, exactly as one `(run)` of the encoding's
        // user rules does -- so at equal round counts the two sides are answering the
        // same question whether or not either has settled.
        println!("SATURATED {}", if saturated { "yes" } else { "no" });
    }

    // The oracle is only useful if the reference graph itself satisfies the
    // implementation's representation invariants.  The `checks` feature also runs
    // these assertions during rebuilding; this final check covers the exact state
    // from which the partition and structured dump are observed.
    // Under `--no-default-features` the crate runs as the paper's experiments ran it,
    // and this walk is skipped with the feature: a timing run wants neither.
    if cfg!(feature = "checks") {
        eg.check();
    }

    // Unlike a probe, a goal is deliberately not inserted before rewriting. This
    // mirrors the paper artifact's `lookup_rec_expr` criterion and prevents the
    // expected result from changing which rewrites match.  Existence alone is not
    // enough: the artifact requires the goal to be equivalent to the initial term.
    for goal in &spec.goals {
        let reached = term_ids
            .first()
            .is_some_and(|start| goal_reached(&eg, start, goal));
        println!("GOAL {}", if reached { "yes" } else { "no" });
    }

    if spec.sizes {
        let ids = eg.ids();
        let nodes: usize = ids.iter().map(|id| eg.enodes(*id).len()).sum();
        println!("SIZES {} {}", ids.len(), nodes);
    }
    if spec.dump {
        if let Err(message) = dump_structured(&eg) {
            eprintln!("REFERENCE_LIMIT: {message}");
            std::process::exit(2);
        }
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
/// A class with more slots than `GROUP_SLOT_CAP` produces an explicit limit rather
/// than a partial dump, since 6! is where this stops being cheap.
fn group_of(eg: &G, id: Id) -> Result<Vec<String>, usize> {
    let mut slots: Vec<Slot> = eg.slots(id).iter().copied().collect();
    slots.sort_by_key(|s| s.to_string());
    if slots.len() > group_slot_cap() {
        return Err(slots.len());
    }
    let ident = SlotMap::identity(&slots.iter().copied().collect());
    let mut out = Vec::new();
    let x = AppliedId::new(id, ident);
    // one permutation at a time (Heap's algorithm), so a wide class costs its
    // factorial in `eq` tests but not in memory
    let mut perm = slots.clone();
    let n = perm.len();
    let mut c = vec![0usize; n];
    let mut try_perm = |perm: &[Slot]| {
        let mut m = SlotMap::new();
        for (a, b) in slots.iter().zip(perm) {
            m.insert(*a, *b);
        }
        let y = AppliedId::new(id, m);
        if eg.eq(&x, &y) {
            let mut parts: Vec<String> = slots
                .iter()
                .zip(perm)
                .map(|(a, b)| format!("{a}>{b}"))
                .collect();
            parts.sort();
            out.push(parts.join("|"));
        }
    };
    try_perm(&perm);
    let mut i = 0;
    while i < n {
        if c[i] < i {
            if i % 2 == 0 {
                perm.swap(0, i);
            } else {
                perm.swap(c[i], i);
            }
            try_perm(&perm);
            c[i] += 1;
            i = 0;
        } else {
            c[i] = 0;
            i += 1;
        }
    }
    out.sort();
    Ok(out)
}

/// Every class and node, in a form the encoding side can be compared against.
///
/// `to_syntax` gives a node as a sequence of operator/payload strings, child
/// invocations and slot literals, so nothing has to be recovered from `Debug`
/// output. Slot *names* are printed as they are; the comparison is what
/// canonicalises them away, since the two sides pick names independently.
fn dump_structured(eg: &G) -> Result<(), String> {
    let mut ids = eg.ids();
    ids.sort_by_key(|i| format!("{i:?}"));

    // Check the bound before writing anything.  A partial dump is especially
    // dangerous to a graph-isomorphism oracle because it can look like a valid,
    // smaller graph.  The caller turns this into a documented nonzero outcome.
    for id in &ids {
        let width = eg.slots(*id).len();
        if width > group_slot_cap() {
            return Err(format!(
                "class {id:?} has {width} live slots; symmetry enumeration is capped at {}",
                group_slot_cap()
            ));
        }
    }

    for id in ids {
        let mut slots: Vec<String> = eg.slots(id).iter().map(|s| s.to_string()).collect();
        slots.sort();
        println!("CLASS {:?} SLOTS {}", id, slots.join(","));
        let group = group_of(eg, id).expect("group width was checked before dumping");
        println!("GROUP {:?} {}", id, group.join(";"));
        let mut lines: Vec<String> = Vec::new();
        for node in eg.enodes(id) {
            let mut parts: Vec<String> = Vec::new();
            for e in node.to_syntax() {
                match e {
                    SyntaxElem::String(t) => parts.push(format!("o:{t}")),
                    SyntaxElem::Slot(s) => parts.push(format!("s:{s}")),
                    SyntaxElem::AppliedId(a) => {
                        // Use one normalized AppliedId for both fields.  Combining
                        // the leader returned by `find_applied_id` with the old map
                        // can express an invocation in two incompatible frames.
                        let a = eg.find_applied_id(&a);
                        let mut m: Vec<String> =
                            a.m.iter().map(|(k, v)| format!("{k}>{v}")).collect();
                        m.sort();
                        parts.push(format!("c:{:?}:{}", a.id, m.join("|")));
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
    Ok(())
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn snapshot_invocation_cannot_capture_a_free_slot() {
        let mut eg = G::default();
        let root = add(&mut eg, "(lam $bound (f (var $bound) (var $free)))");
        Snapshot::take(&eg);
        SNAPSHOT.with(|s| {
            let s = s.borrow();
            let snapshot = s.as_ref().unwrap();
            let node = &snapshot.best[&root.id];
            let bound = *node.private_slots().iter().next().unwrap();
            let free = *eg.slots(root.id).iter().next().unwrap();
            let mut map = SlotMap::new();
            map.insert(free, bound);
            let invocation = AppliedId::new(root.id, map);
            let term = snapshot.term(&invocation).unwrap();
            let result = eg.add_expr(term);
            assert_eq!(result.slots(), [bound].into_iter().collect());
            assert!(eg.eq(&result, &invocation));
            eg.check();
        });
    }

    #[test]
    fn tree_cost_strictly_increases_beyond_machine_sizes() {
        let mut eg = G::default();
        let child = add(&mut eg, "(null)");
        let node = L::F(child.clone(), child.clone());
        let large = BigUint::from(1u8) << 130usize;
        let cost = HashMap::from([(child.id, large.clone())]);
        assert_eq!(ast_size(&node, &cost), Some(&large + &large + 1u8));
        assert!(ast_size(&node, &cost).unwrap() > large);
    }

    #[test]
    fn oversized_group_is_an_explicit_limit() {
        let mut eg = G::default();
        let root = add(
            &mut eg,
            "(f (var $a) (f (var $b) (f (var $c) (f (var $d) (f (var $e) (f (var $f) (var $g)))))))",
        );
        let id = eg.find_applied_id(&root).id;

        assert_eq!(group_of(&eg, id), Err(7));
        assert!(dump_structured(&eg)
            .unwrap_err()
            .contains("symmetry enumeration is capped at 6"));
    }

    #[test]
    fn goal_requires_equivalence_not_only_existence() {
        let mut eg = G::default();
        let start = add(&mut eg, "(null)");
        let other = add(&mut eg, "(f (null) (null))");

        assert!(!goal_reached(&eg, &start, "(f (null) (null))"));
        eg.union(&start, &other);
        assert!(goal_reached(&eg, &start, "(f (null) (null))"));
    }
}
