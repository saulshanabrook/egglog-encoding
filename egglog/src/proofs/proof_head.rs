//! How a rule head lowers, and the flat array of proofs that lowering produces.
//!
//! A head that builds a term needs more proofs than it concludes: the term as
//! the head wrote it, the same term over its children's representatives, and the
//! edges between them. One walk of the head produces them all, in a fixed order,
//! so a proof is named by nothing but its position in that array — its *column*.
//! [`HeadLayout`] is where those columns go. The encoder walks a head to lower
//! it, naming each row it emits by the column the layout gives it; [`Firing`]
//! walks the same head to rebuild the array from the substitution, the body
//! premises, and the rule proof's trailing *bridge* premises — the view-row proof
//! of each subterm the head interned. A row's column indexes straight into what
//! comes back.
//!
//! [`HeadPlan`] is the head as the encoder lowers it, read by both walks;
//! [`ProofAlgebra`] holds the compositions they share, and [`Head`] says which
//! of the encoder's two composing sites it is at (see `proof_encoding.md`).

use crate::{
    TermId,
    ast::{
        FunctionSubtype, GenericAction, GenericExpr, ResolvedAction, ResolvedExpr, ResolvedExprExt,
        ResolvedVar, Span,
    },
    core::ResolvedCall,
    proofs::{
        proof_checker::eval_expr_with_subst,
        proof_encoding::ProofInstrumentor,
        proof_format::{Justification, Proof, ProofId, ProofStore, Proposition, SynthKey},
    },
    typechecking::FuncType,
    util::{HashMap, HashSet, IndexMap},
};

/// One proof a head's walk produces, naming what a column holds.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum HeadProof {
    /// The head's own conclusion about the term written here.
    Own,
    /// That conclusion restated over the children's representatives.
    Canonical,
    /// The term as written equals the e-class the head interned it into.
    Connector,
    /// A construct-into guest's dropped `union`, stated `target = guest`.
    DroppedEdge,
    /// A construct-into guest's view row: the target's e-class equals the guest's
    /// term over its children's representatives.
    GuestView,
    /// A `union`'s union-find edge — the `@UF` row's arrow from a term to its
    /// parent, proving `term = parent` — with the left operand as the term.
    /// Which operand that is comes out of the value ordering at run time, so the
    /// walk produces the edge both ways round.
    EdgeFromLhs,
    /// The same edge with the `union`'s right operand as the term.
    EdgeFromRhs,
}

/// A position a head's walk reaches, which claims one column per proof it
/// produces there.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum HeadPosition {
    /// A term the head builds.
    Built,
    /// A term built into another operand's e-class rather than a fresh one.
    Guest,
    /// Any other call: a primitive, a relation, a global lookup.
    Call,
    /// A `union`.
    Union,
    /// A `set`.
    Set,
}

impl HeadPosition {
    /// The proofs this position produces, in the order the walk produces them.
    pub(crate) fn proofs(self) -> &'static [HeadProof] {
        use HeadProof::*;
        match self {
            HeadPosition::Built => &[Own, Canonical, Connector],
            HeadPosition::Guest => &[Own, DroppedEdge, GuestView, Connector],
            HeadPosition::Call => &[Own],
            HeadPosition::Union => &[Own, EdgeFromLhs, EdgeFromRhs],
            HeadPosition::Set => &[Own],
        }
    }
}

/// The consecutive columns one position claims, one per proof in
/// [`HeadPosition::proofs`].
#[derive(Clone, Copy)]
pub(crate) struct HeadRun {
    position: HeadPosition,
    /// The run's first column.
    first: usize,
}

impl HeadRun {
    /// The column holding `proof`.
    pub(crate) fn column(self, proof: HeadProof) -> usize {
        let offset = self
            .position
            .proofs()
            .iter()
            .position(|held| *held == proof)
            .unwrap_or_else(|| panic!("a {:?} position holds no {proof:?}", self.position));
        self.first + offset
    }
}

/// Where every column of a rule head goes.
///
/// One walk of the [`HeadPlan`] claims a run per position — an action's operands
/// before the action, a term's children before the term — and that walk is the
/// authority: the encoder claims runs from it as it lowers, and [`Firing`] fills
/// them as it walks, each panicking if the position it is at is not the one the
/// layout has there.
#[derive(Clone)]
pub(crate) struct HeadLayout {
    runs: Vec<HeadRun>,
}

impl HeadLayout {
    /// Lay the columns of a planned head out by walking it once.
    fn new(
        actions: &[ResolvedAction],
        construct_into: &HashMap<String, String>,
        dropped: &HashSet<usize>,
    ) -> HeadLayout {
        let mut layout = HeadLayout { runs: vec![] };
        for (at, action) in actions.iter().enumerate() {
            if dropped.contains(&at) {
                continue;
            }
            match action {
                GenericAction::Let(_, var, expr) if construct_into.contains_key(&var.name) => {
                    let (_, args) = constructor_operand(expr)
                        .expect("a construct-into guest is a constructor application");
                    layout.args(args);
                    layout.claim(HeadPosition::Guest);
                }
                GenericAction::Let(_, _, expr) | GenericAction::Expr(_, expr) => layout.expr(expr),
                GenericAction::Union(_, lhs, rhs) => {
                    layout.expr(lhs);
                    layout.expr(rhs);
                    layout.claim(HeadPosition::Union);
                }
                GenericAction::Set(_, _, args, value) => {
                    layout.args(args);
                    layout.expr(value);
                    layout.claim(HeadPosition::Set);
                }
                // A `change` concludes nothing, and a `panic` is passed through
                // uninstrumented, so neither they nor their arguments hold a
                // column.
                GenericAction::Change(..) | GenericAction::Panic(..) => {}
            }
        }
        layout
    }

    /// The run of columns the walk's `position`th position claims.
    fn run(&self, position: usize) -> HeadRun {
        *self
            .runs
            .get(position)
            .unwrap_or_else(|| panic!("a head's walk has no position {position}"))
    }

    /// What the column at `column` holds, or `None` past the head's last column.
    #[cfg(test)]
    pub(crate) fn proof_at(&self, column: usize) -> Option<HeadProof> {
        let run = self.runs.iter().rev().find(|run| run.first <= column)?;
        run.position.proofs().get(column - run.first).copied()
    }

    fn expr(&mut self, expr: &ResolvedExpr) {
        let ResolvedExpr::Call(_, _, args) = expr else {
            // A variable or a literal builds nothing, so it is not a position.
            return;
        };
        self.args(args);
        self.claim(match constructor_operand(expr) {
            Some(_) => HeadPosition::Built,
            None => HeadPosition::Call,
        });
    }

    fn args(&mut self, args: &[ResolvedExpr]) {
        for arg in args {
            self.expr(arg);
        }
    }

    fn claim(&mut self, position: HeadPosition) {
        let first = self
            .runs
            .last()
            .map_or(0, |run| run.first + run.position.proofs().len());
        self.runs.push(HeadRun { position, first });
    }
}

/// Which of the encoding's two layers the encoder is lowering under (see the
/// *Proofs* part of `proof_encoding.md`).
enum ProofSite {
    /// No rule head to replay: a top-level action, a merge body, or a position
    /// inside a head that concludes nothing — a `change` argument.
    Composed,
    /// A rule head, whose columns `layout` lays out, at its `next_position`th
    /// position.
    Skeleton {
        layout: HeadLayout,
        next_position: usize,
    },
}

/// One block of actions as the encoder lowers it: which layer its statements
/// are on, and what its next rule proof row chains onto. One is made per block,
/// so nothing it holds reaches the next.
pub(crate) struct Head {
    site: ProofSite,
    /// The last rule proof row this head minted.
    last: Option<String>,
    /// The row minted just before the head's newest interning, carrying every
    /// bridge before that one, and that interning's bridge — the interned
    /// subterm's view-row proof. `None` until the head interns something.
    link: Option<(String, String)>,
}

impl Head {
    /// A rule head laid out by `layout`, before its first position.
    pub(crate) fn skeleton(layout: HeadLayout) -> Head {
        Head::at(ProofSite::Skeleton {
            layout,
            next_position: 0,
        })
    }

    /// A block with no rule head to replay, whose proofs are composed on the
    /// spot.
    pub(crate) fn composed() -> Head {
        Head::at(ProofSite::Composed)
    }

    fn at(site: ProofSite) -> Head {
        Head {
            site,
            last: None,
            link: None,
        }
    }

    /// Whether the proofs here are composed on the spot rather than numbered.
    pub(crate) fn composes(&self) -> bool {
        matches!(self.site, ProofSite::Composed)
    }

    /// Claim the columns of the next position, which must be a `position`, or
    /// `None` where the head composes instead of numbering.
    pub(crate) fn claim(&mut self, position: HeadPosition) -> Option<HeadRun> {
        let ProofSite::Skeleton {
            layout,
            next_position,
        } = &mut self.site
        else {
            return None;
        };
        let run = layout.run(*next_position);
        assert_eq!(
            run.position, position,
            "the encoder is lowering a {position:?} at position {next_position}, \
             where the head's layout has a {:?}",
            run.position
        );
        *next_position += 1;
        Some(run)
    }

    /// Run `lower` at a position the head concludes nothing about — a `change`
    /// argument — whose proofs compose rather than claim columns. The head's
    /// numbering resumes afterwards, over the same chain.
    pub(crate) fn composing<R>(&mut self, lower: impl FnOnce(&mut Head) -> R) -> R {
        let numbered = std::mem::replace(&mut self.site, ProofSite::Composed);
        let lowered = lower(self);
        self.site = numbered;
        lowered
    }

    /// What the next rule proof row chains onto, per [`Self::record_bridge`].
    pub(crate) fn link(&self) -> Option<(String, String)> {
        self.link.clone()
    }

    /// Record `proof` as the head's newest rule proof row.
    pub(crate) fn minted(&mut self, proof: &str) {
        self.last = Some(proof.to_string());
    }

    /// Record a subterm's view-row proof as a bridge premise of the rule proofs
    /// minted from here on. A composing position records nothing: it has already
    /// used the proof, and a subterm the head concludes nothing about — a nested
    /// `change` argument — is not in the array conversion rebuilds.
    pub(crate) fn record_bridge(&mut self, view_proof: &str) {
        if self.composes() {
            return;
        }
        let prev = self
            .last
            .clone()
            .expect("a head states the term it is interning before interning it");
        self.link = Some((prev, view_proof.to_string()));
    }
}

/// A rule head as the encoder lowers it.
pub(crate) struct HeadPlan {
    /// The head with every constructor-application `union` operand lifted into a
    /// preceding `let`.
    pub actions: Vec<ResolvedAction>,
    /// Guest variable -> the variable holding the e-class its constructor is
    /// built into, instead of a fresh one.
    pub construct_into: HashMap<String, String>,
    /// Indices into [`Self::actions`] of the `union`s the plan makes redundant.
    pub dropped: HashSet<usize>,
    /// Where this head's columns go.
    pub layout: HeadLayout,
}

impl HeadPlan {
    /// Plan `actions`. `fresh` names the lifted `let`s; only their uniqueness
    /// matters, so a consumer that wants the shape rather than the code can
    /// supply a local counter.
    pub(crate) fn new(actions: &[ResolvedAction], fresh: &mut dyn FnMut() -> String) -> Self {
        let actions = normalize_union_operands(actions, fresh);
        let (construct_into, dropped) = plan_construct_into(&actions);
        let layout = HeadLayout::new(&actions, &construct_into, &dropped);
        HeadPlan {
            actions,
            construct_into,
            dropped,
            layout,
        }
    }
}

/// The `(FuncType, args)` of a constructor-application expression, else `None`.
pub(crate) fn constructor_operand(expr: &ResolvedExpr) -> Option<(&FuncType, &[ResolvedExpr])> {
    match expr {
        ResolvedExpr::Call(_, ResolvedCall::Func(func_type), args)
            if func_type.subtype == FunctionSubtype::Constructor =>
        {
            Some((func_type, args.as_slice()))
        }
        _ => None,
    }
}

/// The row a `set` writes, as a call the head can evaluate: a custom function
/// stores its output as the last argument.
fn set_row_expr(
    span: &Span,
    func: &ResolvedCall,
    args: &[ResolvedExpr],
    value: &ResolvedExpr,
) -> ResolvedExpr {
    let mut row = args.to_vec();
    row.push(value.clone());
    ResolvedExpr::Call(span.clone(), func.clone(), row)
}

/// Lift each constructor-application `union` operand into a preceding `let`, so
/// that every `union` operand [`plan_construct_into`] sees is a variable.
fn normalize_union_operands(
    actions: &[ResolvedAction],
    fresh: &mut dyn FnMut() -> String,
) -> Vec<ResolvedAction> {
    let mut out = vec![];
    for action in actions {
        match action {
            ResolvedAction::Union(span, lhs, rhs) => {
                let lhs = lift_union_operand(lhs.clone(), &mut out, fresh);
                let rhs = lift_union_operand(rhs.clone(), &mut out, fresh);
                out.push(ResolvedAction::Union(span.clone(), lhs, rhs));
            }
            other => out.push(other.clone()),
        }
    }
    out
}

/// If `operand` is a constructor application, bind it to a fresh `let` (pushed
/// onto `out`) and return a variable referencing it; otherwise return `operand`
/// unchanged.
fn lift_union_operand(
    operand: ResolvedExpr,
    out: &mut Vec<ResolvedAction>,
    fresh: &mut dyn FnMut() -> String,
) -> ResolvedExpr {
    if constructor_operand(&operand).is_none() {
        return operand;
    }
    let span = operand.span();
    let var = ResolvedVar {
        name: fresh(),
        sort: operand.output_type(),
        is_global_ref: false,
    };
    out.push(ResolvedAction::Let(span.clone(), var.clone(), operand));
    GenericExpr::Var(span, var)
}

/// Plan the construct-into optimization over normalized actions (union operands
/// are variables). Returns a map from each guest variable — whose constructor is
/// built into the target's e-class instead of a fresh one — to the target
/// variable, and the set of union action indices it makes redundant.
///
/// Conservative: only a `union` of two distinct, not-yet-touched variables where
/// at least one is a constructor-`let` is optimized. The guest is the
/// later-defined constructor operand (so the target's e-class is already bound
/// where the guest is built); a matched (un-`let`) variable is always an eligible
/// target.
fn plan_construct_into(actions: &[ResolvedAction]) -> (HashMap<String, String>, HashSet<usize>) {
    let mut all_def: HashMap<String, usize> = HashMap::default();
    let mut ctor_def: HashMap<String, usize> = HashMap::default();
    for (i, action) in actions.iter().enumerate() {
        if let ResolvedAction::Let(_, v, expr) = action {
            all_def.insert(v.name.clone(), i);
            if constructor_operand(expr).is_some() {
                ctor_def.insert(v.name.clone(), i);
            }
        }
    }

    let mut construct_into: HashMap<String, String> = HashMap::default();
    let mut dropped: HashSet<usize> = HashSet::default();
    let mut used: HashSet<String> = HashSet::default();
    for (i, action) in actions.iter().enumerate() {
        let ResolvedAction::Union(_, lhs, rhs) = action else {
            continue;
        };
        let (GenericExpr::Var(_, va), GenericExpr::Var(_, vb)) = (lhs, rhs) else {
            continue;
        };
        let (a, b) = (va.name.clone(), vb.name.clone());
        if a == b {
            // Union of a variable with itself is a no-op.
            dropped.insert(i);
            continue;
        }
        if used.contains(&a) || used.contains(&b) {
            // Keep chains of optimized unions out of scope for now.
            continue;
        }
        let (guest, target) = match (ctor_def.get(&a), ctor_def.get(&b)) {
            (Some(&ia), Some(&ib)) => {
                if ia >= ib {
                    (a.clone(), b)
                } else {
                    (b, a.clone())
                }
            }
            (Some(_), None) => (a.clone(), b),
            (None, Some(_)) => (b, a.clone()),
            (None, None) => continue,
        };
        // The target's e-class must be bound where the guest is built: a matched
        // variable always is; a `let` must precede the guest's.
        let guest_idx = ctor_def[&guest];
        if let Some(&target_idx) = all_def.get(&target)
            && target_idx >= guest_idx
        {
            continue;
        }
        used.insert(guest.clone());
        used.insert(target.clone());
        construct_into.insert(guest, target);
        dropped.insert(i);
    }
    (construct_into, dropped)
}

/// How far a rule head's walk has got, and everything it produced on the way.
///
/// Each rule proof of a firing walks the head only as far as its own bridges
/// reach, and hands what it produced to the next one, which carries on from
/// there. What it holds is what the whole walk would have produced this far.
#[derive(Clone, Default)]
pub(crate) struct HeadWalk {
    /// The action to carry on at.
    next_action: usize,
    /// How many of the layout's positions the walk has reached.
    next_position: usize,
    /// How many bridges the walk has taken from the row's supply.
    bridges_taken: usize,
    /// The columns filled so far. `None` at a column the walk numbers but the
    /// head produces no proof for.
    proofs: Vec<Option<ProofId>>,
    /// What the head's variables stand for, as the walk binds them. Empty until
    /// the first walk, which seeds it with the globals and the substitution.
    bindings: HashMap<String, TermId>,
    /// A variable holding a term the head built -> that term's connector.
    connectors: HashMap<String, ProofId>,
}

impl HeadWalk {
    /// How far into the head this walk got.
    pub(crate) fn reaches(&self) -> usize {
        self.next_action
    }

    /// How many bridges the walk took, which is where a row carrying on from it
    /// starts taking from its own supply.
    pub(crate) fn bridges_taken(&self) -> usize {
        self.bridges_taken
    }

    /// Where the walk stands, to come back to with [`Self::rewind`].
    fn mark(&self) -> ActionStart {
        ActionStart {
            action: self.next_action,
            position: self.next_position,
            bridges: self.bridges_taken,
            columns: self.proofs.len(),
        }
    }

    /// Undo everything the walk did after `mark`. The bindings and connectors it
    /// wrote are left alone: an action rewrites its own before anything reads
    /// them, and the actions after it are unreached either way.
    fn rewind(&mut self, mark: ActionStart) {
        self.next_action = mark.action;
        self.next_position = mark.position;
        self.bridges_taken = mark.bridges;
        self.proofs.truncate(mark.columns);
    }
}

/// The action boundary a walk can be put back to.
#[derive(Clone, Copy, Default)]
struct ActionStart {
    action: usize,
    position: usize,
    bridges: usize,
    columns: usize,
}

/// One firing of a rule head, and the flat array of proofs its lowering produces.
///
/// Each position of the walk fills the run of columns [`HeadLayout`] gives it,
/// in the order [`HeadPosition::proofs`] lists them. The array lives in a
/// [`HeadWalk`], which one rule proof of the firing hands on to the next.
pub(crate) struct Firing<'a> {
    rule_name: &'a str,
    plan: &'a HeadPlan,
    /// The position being filled, and how many of its columns are filled.
    open: Option<(HeadRun, usize)>,
    /// The premises the rule body matched, one per body fact.
    body_premises: Vec<ProofId>,
    substitution: IndexMap<String, TermId>,
    /// The bridges the requesting rule proof row carries, in the order the head
    /// interned them, each asked for with the proof of the term being interned.
    /// The supply runs dry inside the action the row was minted in.
    bridges: Box<dyn FnMut(&mut ProofStore, ProofId) -> Option<ProofId> + 'a>,
    walk: HeadWalk,
    /// Where the action being walked began.
    action_start: ActionStart,
    /// Whether the walk has asked for a bridge past the ones this row carries.
    dry: bool,
}

impl<'a> Firing<'a> {
    /// `bindings` must resolve every variable the head reads — the globals plus
    /// the body's substitution — unless a walk is handed to [`Self::carry_on`],
    /// which brings its own. `bridges` hands them over one at a time, starting
    /// where that walk stopped taking.
    pub(crate) fn new(
        rule_name: &'a str,
        plan: &'a HeadPlan,
        bindings: HashMap<String, TermId>,
        body_premises: Vec<ProofId>,
        substitution: IndexMap<String, TermId>,
        bridges: Box<dyn FnMut(&mut ProofStore, ProofId) -> Option<ProofId> + 'a>,
    ) -> Self {
        Firing {
            rule_name,
            plan,
            open: None,
            body_premises,
            substitution,
            bridges,
            walk: HeadWalk {
                bindings,
                ..HeadWalk::default()
            },
            action_start: ActionStart::default(),
            dry: false,
        }
    }

    /// Carry on from `walk`, which an earlier row of this firing left behind.
    pub(crate) fn carry_on(&mut self, walk: HeadWalk) {
        self.walk = walk;
    }

    /// The walk to hand the next row of this firing. The action the supply ran
    /// dry in is put back, so the next row walks it with the bridge it wanted.
    pub(crate) fn into_walk(mut self) -> HeadWalk {
        if self.dry {
            self.walk.rewind(self.action_start);
        }
        self.walk
    }

    /// Every proof the head's lowering produces, by column. `None` at a column
    /// the walk numbers but the head produces no proof for.
    #[cfg(test)]
    pub(crate) fn proofs(&mut self, store: &mut ProofStore) -> &[Option<ProofId>] {
        self.fill(store);
        &self.walk.proofs
    }

    /// The proof the e-graph stored in the column `raw` names.
    pub(crate) fn column(&mut self, store: &mut ProofStore, raw: i64) -> ProofId {
        let rule_name = self.rule_name;
        let column = usize::try_from(raw).unwrap_or_else(|_| {
            panic!("rule {rule_name} proof was emitted without a column ({raw})")
        });
        self.fill(store);
        self.walk
            .proofs
            .get(column)
            .copied()
            .flatten()
            .unwrap_or_else(|| {
                panic!("rule {rule_name}'s head produces no proof at column {column}")
            })
    }

    /// Walk the head as far as this row's bridges reach: to the end of the action
    /// that asks for one past them, which is the action the row was minted in.
    fn fill(&mut self, store: &mut ProofStore) {
        let plan = self.plan;
        while !self.dry && self.walk.next_action < plan.actions.len() {
            self.action_start = self.walk.mark();
            let at = self.walk.next_action;
            self.walk.next_action += 1;
            if plan.dropped.contains(&at) {
                continue;
            }
            match &plan.actions[at] {
                GenericAction::Let(_, var, expr) => {
                    let connector = match self.plan.construct_into.get(&var.name) {
                        Some(target) => self.guest(store, expr, target),
                        None => self.expr(store, expr),
                    };
                    let term = self.eval(store, expr);
                    self.walk.bindings.insert(var.name.clone(), term);
                    if let Some(connector) = connector {
                        self.walk.connectors.insert(var.name.clone(), connector);
                    }
                }
                GenericAction::Expr(_, expr) => {
                    self.expr(store, expr);
                }
                GenericAction::Union(_, lhs, rhs) => {
                    let lhs_connector = self.expr(store, lhs);
                    let rhs_connector = self.expr(store, rhs);
                    let lhs_term = self.eval(store, lhs);
                    let rhs_term = self.eval(store, rhs);
                    self.claim(HeadPosition::Union, |this| {
                        let own =
                            this.own(store, HeadProof::Own, Proposition::new(lhs_term, rhs_term));
                        match (lhs_connector, rhs_connector) {
                            // Nothing was built, so both endpoints' terms are the
                            // ones the head concluded over and the edge is that
                            // conclusion, in whichever direction the union-find
                            // asks for.
                            (None, None) => {
                                this.own(
                                    store,
                                    HeadProof::EdgeFromLhs,
                                    Proposition::new(lhs_term, rhs_term),
                                );
                                this.own(
                                    store,
                                    HeadProof::EdgeFromRhs,
                                    Proposition::new(rhs_term, lhs_term),
                                );
                            }
                            operands => this.union_edge(store, own, operands),
                        }
                    });
                }
                GenericAction::Set(span, func, args, value) => {
                    for arg in args {
                        self.expr(store, arg);
                    }
                    self.expr(store, value);
                    let row = set_row_expr(span, func, args, value);
                    let row_term = self.eval(store, &row);
                    self.claim(HeadPosition::Set, |this| {
                        this.own(store, HeadProof::Own, Proposition::new(row_term, row_term));
                    });
                }
                GenericAction::Change(..) | GenericAction::Panic(..) => {}
            }
        }
    }

    /// Walk `expr`, and answer with its connector when it holds a term the head
    /// built.
    fn expr(&mut self, store: &mut ProofStore, expr: &ResolvedExpr) -> Option<ProofId> {
        let ResolvedExpr::Call(_, _, args) = expr else {
            // A variable's value comes from wherever it was bound; a literal
            // holds no built term.
            return match expr {
                ResolvedExpr::Var(_, var) => self.walk.connectors.get(&var.name).copied(),
                _ => None,
            };
        };
        let steps = self.args(store, args);
        let term = self.eval(store, expr);
        // A primitive or a global lookup builds nothing itself, though a
        // constructor argument of it is still built.
        let builds = constructor_operand(expr).is_some();
        let position = if builds {
            HeadPosition::Built
        } else {
            HeadPosition::Call
        };
        self.claim(position, |this| {
            let own = this.own(store, HeadProof::Own, Proposition::new(term, term));
            if !builds {
                return None;
            }
            let to_canonical = store.canonicalize(own, steps);
            let canonical_reflexive = store.reflexive(to_canonical);
            this.push(HeadProof::Canonical, Some(canonical_reflexive));
            let connector = match this.bridge(store, to_canonical) {
                Some(bridge) => store.connect(to_canonical, bridge),
                None => to_canonical,
            };
            this.push(HeadProof::Connector, Some(connector));
            Some(connector)
        })
    }

    /// Walk a construct-into guest, whose constructor is built into `target`'s
    /// e-class: the dropped `union`'s edge stands in for the interning row, and
    /// the guest's view row states that e-class equals the guest's term.
    fn guest(
        &mut self,
        store: &mut ProofStore,
        expr: &ResolvedExpr,
        target: &str,
    ) -> Option<ProofId> {
        let (_, args) =
            constructor_operand(expr).expect("a construct-into guest is a constructor application");
        let steps = self.args(store, args);
        let term = self.eval(store, expr);
        self.claim(HeadPosition::Guest, |this| {
            let own = this.own(store, HeadProof::Own, Proposition::new(term, term));
            let to_canonical = store.canonicalize(own, steps);
            let target_term = *this.walk.bindings.get(target).unwrap_or_else(|| {
                panic!(
                    "rule {}'s construct-into target {target} is unbound",
                    this.rule_name
                )
            });
            let edge = this.own(
                store,
                HeadProof::DroppedEdge,
                Proposition::new(target_term, term),
            );
            let target_connector = this.walk.connectors.get(target).copied();
            let view = store.guest_view(edge, to_canonical, target_connector);
            this.push(HeadProof::GuestView, Some(view));
            let connector = store.connect(to_canonical, view);
            this.push(HeadProof::Connector, Some(connector));
            Some(connector)
        })
    }

    /// Walk a call's arguments, keeping the connector of each one holding a term
    /// the head built, at the position it sits in the call.
    fn args(&mut self, store: &mut ProofStore, args: &[ResolvedExpr]) -> Vec<(usize, ProofId)> {
        let mut steps = vec![];
        for (index, arg) in args.iter().enumerate() {
            if let Some(connector) = self.expr(store, arg) {
                steps.push((index, connector));
            }
        }
        steps
    }

    /// A `union`'s union-find edge, routed through the operands' written forms so
    /// both endpoints' proofs end at one shared term.
    fn union_edge(
        &mut self,
        store: &mut ProofStore,
        own: ProofId,
        operands: (Option<ProofId>, Option<ProofId>),
    ) {
        let (lhs, rhs) = operands;
        let (lhs_to, rhs_to) = store.union_to_shared(own, lhs, rhs);
        for (from, max_pf, min_pf) in [
            (HeadProof::EdgeFromLhs, lhs_to, rhs_to),
            (HeadProof::EdgeFromRhs, rhs_to, lhs_to),
        ] {
            let back = sym(store, min_pf);
            let edge = trans(store, max_pf, back);
            self.push(from, Some(edge));
        }
    }

    /// Fill the run of columns the layout gives this walk's next position, which
    /// must be a `position`.
    fn claim<R>(&mut self, position: HeadPosition, fill: impl FnOnce(&mut Self) -> R) -> R {
        let run = self.plan.layout.run(self.walk.next_position);
        assert_eq!(
            run.position, position,
            "rule {}'s walk is at a {position:?} where its layout has a {:?}",
            self.rule_name, run.position
        );
        assert_eq!(
            self.walk.proofs.len(),
            run.first,
            "rule {}'s walk reached the {:?} the layout puts at column {}, having filled {}",
            self.rule_name,
            position,
            run.first,
            self.walk.proofs.len()
        );
        self.walk.next_position += 1;
        let outer = self.open.replace((run, 0));
        assert!(outer.is_none(), "a head's positions do not nest");
        let out = fill(self);
        let (_, produced) = self.open.take().expect("the position stayed open");
        assert_eq!(
            produced,
            position.proofs().len(),
            "rule {}'s walk produced {produced} of a {position:?}'s {} proofs",
            self.rule_name,
            position.proofs().len()
        );
        out
    }

    /// Fill the open position's next column, which the layout says holds `proof`.
    fn push(&mut self, proof: HeadProof, id: Option<ProofId>) {
        let (run, produced) = self
            .open
            .as_mut()
            .expect("every proof the walk produces belongs to a position");
        assert_eq!(
            run.position.proofs().get(*produced),
            Some(&proof),
            "rule {}'s walk produced a {proof:?} where a {:?} holds {:?}",
            self.rule_name,
            run.position,
            run.position.proofs().get(*produced)
        );
        *produced += 1;
        self.walk.proofs.push(id);
    }

    /// The head's own conclusion, at the column holding `proof`.
    fn own(
        &mut self,
        store: &mut ProofStore,
        proof: HeadProof,
        proposition: Proposition,
    ) -> ProofId {
        let column = self.walk.proofs.len() as i64;
        let id = store.push_shared_proof(
            SynthKey::Rule(
                self.rule_name.to_string(),
                column,
                self.body_premises.clone(),
            ),
            Proof {
                proposition,
                justification: Justification::Rule {
                    name: self.rule_name.to_string(),
                    premise_proofs: self.body_premises.clone(),
                    substitution: self.substitution.clone(),
                },
            },
        );
        self.push(proof, Some(id));
        id
    }

    /// The term `expr` evaluates to under the bindings in effect.
    fn eval(&mut self, store: &mut ProofStore, expr: &ResolvedExpr) -> TermId {
        eval_expr_with_subst(
            self.rule_name,
            expr,
            &mut store.term_dag,
            &self.walk.bindings,
        )
        .unwrap_or_else(|err| panic!("rule {}'s head did not replay: {err}", self.rule_name))
        .0
    }

    /// The next bridge off the supply: the view-row proof the head recorded for
    /// the term the walk just built, saying which e-class it interned into.
    ///
    /// `None` once the supply has run dry, which ends the walk.
    fn bridge(&mut self, store: &mut ProofStore, to_canonical: ProofId) -> Option<ProofId> {
        let taken = self.walk.bridges_taken;
        self.walk.bridges_taken += 1;
        let Some(bridge) = (self.bridges)(store, to_canonical) else {
            self.dry = true;
            return None;
        };
        // Every proof this read can return — an existing row's, a rebuilt row's, a
        // construct-into guest view, or the encoder's `can_prf` fallback — ends at
        // the canonical term. A bridge that does not is one aligned to the wrong
        // term, which would otherwise compose into a proof of the wrong equality.
        assert_eq!(
            store.get(bridge).rhs(),
            store.get(to_canonical).rhs(),
            "rule {}'s bridge {taken} does not end at the canonical term",
            self.rule_name
        );
        Some(bridge)
    }
}

/// Layer 1: the equality axioms, plus the four compositions a head's lowering
/// builds out of them.
///
/// Walking a head bottom-up and applying [`Self::canonicalize`],
/// [`Self::reflexive`], [`Self::connect`] and [`Self::guest_view`] — with
/// [`Self::union_to_shared`] for a `union`'s two orientations — is the whole of
/// layer 1.
pub(super) trait ProofAlgebra {
    type Proof: Clone;

    /// `p : a = b` reversed to `b = a`.
    fn sym(&mut self, proof: Self::Proof) -> Self::Proof;
    /// `a = b` and `b = c` joined into `a = c`.
    fn trans(&mut self, left: Self::Proof, right: Self::Proof) -> Self::Proof;
    /// `base`'s right-hand side with the child at `child` rewritten by `step`.
    fn congr(&mut self, base: Self::Proof, child: usize, step: Self::Proof) -> Self::Proof;

    /// The proof that a term the head wrote equals the same term over its
    /// children's representatives: one `congr` per child the head built.
    fn canonicalize(
        &mut self,
        own: Self::Proof,
        children: impl IntoIterator<Item = (usize, Self::Proof)>,
    ) -> Self::Proof {
        let mut to_canonical = own;
        for (child, step) in children {
            to_canonical = self.congr(to_canonical, child, step);
        }
        to_canonical
    }

    /// `t = t` for the term `to_canonical` reaches.
    fn reflexive(&mut self, to_canonical: Self::Proof) -> Self::Proof {
        let back = self.sym(to_canonical.clone());
        self.trans(back, to_canonical)
    }

    /// A built term's connector, from the term as written to the e-class the head
    /// interned it into: `dedup` states that e-class equals the canonical term, so
    /// the connector runs through the canonical term and back.
    fn connect(&mut self, to_canonical: Self::Proof, dedup: Self::Proof) -> Self::Proof {
        let back = self.sym(dedup);
        self.trans(to_canonical, back)
    }

    /// Both operands of a `union` routed to one shared term, so the union-find
    /// edge can be composed in either orientation. `own` states the union's own
    /// conclusion `lhs = rhs`, and an operand's connector is present when the head
    /// built that operand; at least one of them must have been.
    fn union_to_shared(
        &mut self,
        own: Self::Proof,
        lhs: Option<Self::Proof>,
        rhs: Option<Self::Proof>,
    ) -> (Self::Proof, Self::Proof) {
        match rhs {
            Some(rhs) => {
                let lhs_to = match lhs {
                    Some(lhs) => {
                        let back = self.sym(lhs);
                        self.trans(back, own)
                    }
                    None => own,
                };
                let rhs_to = self.sym(rhs);
                (lhs_to, rhs_to)
            }
            None => {
                let lhs = lhs.expect("one operand of the union was built");
                let lhs_to = self.sym(lhs);
                let rhs_to = self.sym(own);
                (lhs_to, rhs_to)
            }
        }
    }

    /// A construct-into guest's view-row proof: the target's e-class equals the
    /// guest's term over its children's representatives. `edge` is the dropped
    /// `union`'s equality stated `target = guest`, and `target` the target's own
    /// connector when the head built it too.
    fn guest_view(
        &mut self,
        edge: Self::Proof,
        to_canonical: Self::Proof,
        target: Option<Self::Proof>,
    ) -> Self::Proof {
        let to_dedup = self.trans(edge, to_canonical);
        match target {
            Some(target) => {
                let back = self.sym(target);
                self.trans(back, to_dedup)
            }
            None => to_dedup,
        }
    }
}

/// Applying the algebra builds the proof.
impl ProofAlgebra for ProofStore {
    type Proof = ProofId;

    fn sym(&mut self, proof: ProofId) -> ProofId {
        sym(self, proof)
    }

    fn trans(&mut self, left: ProofId, right: ProofId) -> ProofId {
        trans(self, left, right)
    }

    fn congr(&mut self, base: ProofId, child: usize, step: ProofId) -> ProofId {
        congr(self, base, child, step)
    }
}

/// Applying the algebra emits the proof: each step is a row, named by the
/// variable it binds.
impl ProofAlgebra for ProofInstrumentor<'_> {
    type Proof = String;

    fn sym(&mut self, proof: String) -> String {
        self.mint_sym(&proof)
    }

    fn trans(&mut self, left: String, right: String) -> String {
        self.mint_trans(&left, &right)
    }

    fn congr(&mut self, base: String, child: usize, step: String) -> String {
        self.mint_congr(&base, child, &step)
    }
}

/// `Sym(p)`: `p : a = b` reversed to `b = a`.
pub(super) fn sym(store: &mut ProofStore, proof: ProofId) -> ProofId {
    let prop = store.get(proof).proposition().clone();
    store.push_shared_proof(
        SynthKey::Sym(proof),
        Proof {
            proposition: Proposition::new(prop.rhs, prop.lhs),
            justification: Justification::Sym(proof),
        },
    )
}

/// `Trans(left, right)`. Panics unless the two meet at the same middle term.
pub(super) fn trans(store: &mut ProofStore, left: ProofId, right: ProofId) -> ProofId {
    let lhs = store.get(left).lhs();
    let rhs = store.get(right).rhs();
    assert_eq!(
        store.get(left).rhs(),
        store.get(right).lhs(),
        "transitivity requires matching middle terms"
    );
    store.push_shared_proof(
        SynthKey::Trans(left, right),
        Proof {
            proposition: Proposition::new(lhs, rhs),
            justification: Justification::Trans(left, right),
        },
    )
}

/// `Congr(base, child_index, child_proof)`: `base`'s right-hand side with the
/// child at `child_index` rewritten by `child_proof`.
pub(super) fn congr(
    store: &mut ProofStore,
    base: ProofId,
    child_index: usize,
    child_proof: ProofId,
) -> ProofId {
    let lhs = store.get(base).lhs();
    let base_rhs = store.get(base).rhs();
    let child_rhs = store.get(child_proof).rhs();
    let rhs = store.replace_term_child(base_rhs, child_index, child_rhs);
    store.push_shared_proof(
        SynthKey::Congr(base, child_index, child_proof),
        Proof {
            proposition: Proposition::new(lhs, rhs),
            justification: Justification::Congr {
                proof: base,
                child_index,
                child_proof,
            },
        },
    )
}
