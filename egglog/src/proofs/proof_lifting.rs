//! Temporary state for replaying recorded proofs into a source proof arena.
//! Plans and partially replayed rule firings are temporary. A ground request may
//! lend its raw-ID memo to successive lifters; the checker never consults it.

use super::{
    proof_checker::{
        ProofCheckError, ProofCheckErrorKind, eval_expr_with_subst, eval_merge_expr, run_merge,
    },
    proof_encoding_helpers::{EncodingNames, holds_sort, recomputable_premises},
    proof_format::{
        Justification, Proof, ProofId, ProofStore, Proposition, RawProof, RawProofId,
        RawProofStore, RecordedProofs,
    },
    proof_head::{Firing, HeadPlan, HeadWalk, ProofAlgebra},
};
use crate::{
    ResolvedCall, Term, TermDag, TermId,
    ast::{
        FunctionSubtype, GenericNCommand, ResolvedExpr, ResolvedFact, ResolvedNCommand,
        ResolvedRule,
    },
    typechecking::PrimitiveValidator,
    util::{HEntry, HashMap, HashSet, IEntry, IndexMap},
};
use egglog_numeric_id::DenseIdMap;
use std::rc::Rc;

/// The recorded source position of a proof being lifted. All references are
/// valid only during the visitor call; the proof store retains no positions.
pub enum ProofOrigin<'a> {
    /// A term built by a global action. `path` starts with its original operand
    /// index, followed by child indices. An empty path denotes a `set` row.
    GlobalTerm {
        program: &'a [ResolvedNCommand],
        action: usize,
        path: &'a [usize],
    },
    /// A top-level union, optionally read in reverse operand order.
    GlobalUnion {
        program: &'a [ResolvedNCommand],
        action: usize,
        swapped: bool,
    },
    /// A rule-head conclusion, at an action and operand path in the original head.
    Rule {
        program: &'a [ResolvedNCommand],
        rule: &'a crate::ast::ResolvedRule,
        action: usize,
        path: &'a [usize],
    },
}

/// Receives source positions after the proof DAG is complete, before temporary
/// lifting state is discarded. Global inputs follow action order and precede rule heads;
/// rule conclusions follow proof-ID order. IDs remain valid in the returned store.
pub type ProofVisitor<'a> = dyn FnMut(&ProofStore, ProofId, ProofOrigin<'_>) + 'a;

/// Lift an extracted proof into a proof of the source program.
pub(crate) fn lift_proof(
    encoding_names: &EncodingNames,
    term_dag: TermDag,
    proof_term: TermId,
    prog: &[ResolvedNCommand],
    container_normalizers: HashMap<String, PrimitiveValidator>,
    prim_value_constructors: HashSet<String>,
    visit: Option<&mut ProofVisitor<'_>>,
) -> (ProofStore, ProofId) {
    let (raw_store, root) = RawProofStore::from_extracted(encoding_names, term_dag, proof_term);
    let (store, roots) = ProofStore::lift(
        prog,
        &raw_store,
        &[root],
        container_normalizers,
        prim_value_constructors,
        visit,
    );
    (store, roots[0])
}

impl RawProofStore {
    /// Decode raw roots in the supplied order, optionally visiting source origins.
    /// Panics if a root or its proof is invalid for `program`.
    pub(super) fn lift_with(
        &self,
        program: &[ResolvedNCommand],
        roots: &[RawProofId],
        normalizers: HashMap<String, PrimitiveValidator>,
        value_heads: HashSet<String>,
        visit: Option<&mut ProofVisitor<'_>>,
    ) -> (ProofStore, Vec<ProofId>) {
        ProofStore::lift(program, self, roots, normalizers, value_heads, visit)
    }
}

impl RecordedProofs {
    /// Return unchecked, unsimplified proofs in root order, visiting their source positions.
    /// The caller must check them; `graph` must preserve the command-history prefix at capture.
    pub fn lift_with_visitor(
        &self,
        graph: &crate::EGraph,
        visit: &mut ProofVisitor<'_>,
    ) -> (ProofStore, Vec<ProofId>) {
        self.lift(graph, Some(visit))
    }

    pub(super) fn lift(
        &self,
        graph: &crate::EGraph,
        visit: Option<&mut ProofVisitor<'_>>,
    ) -> (ProofStore, Vec<ProofId>) {
        self.raw.lift_with(
            &graph.proof_check_program[..self.program_len],
            &self.roots,
            self.normalizers.clone(),
            self.value_heads.clone(),
            visit,
        )
    }
}

/// Find the subexpression at pre-order position `idx` in `expr`'s tree (index 0
/// is `expr` itself). Must mirror the indexing the proof encoder uses to tag
/// `MergeFnIdx` proofs.
fn subexpr_at_index(expr: &ResolvedExpr, idx: usize) -> Option<&ResolvedExpr> {
    let mut counter = 0;
    fn walk<'a>(
        expr: &'a ResolvedExpr,
        target: usize,
        counter: &mut usize,
    ) -> Option<&'a ResolvedExpr> {
        if *counter == target {
            return Some(expr);
        }
        *counter += 1;
        if let ResolvedExpr::Call(_, _, args) = expr {
            for arg in args {
                if let Some(found) = walk(arg, target, counter) {
                    return Some(found);
                }
            }
        }
        None
    }
    walk(expr, idx, &mut counter)
}

/// Run subexpression `idx` of a function's merge body with `old`/`new` bound to
/// `old_term`/`new_term`, returning the resulting term. `idx` is a pre-order
/// index over the merge body tree (see [`subexpr_at_index`]); `idx == 0` is the
/// whole body. Evaluating the subexpression reconstructs the term the FD
/// custom-function view merge minted at that position, so each nested
/// merge-body subexpression yields its own conclusion. Used when lifting a
/// `MergeFnIdx` raw proof into its `MergeFn` conclusion.
fn run_merge_subexpr(
    term_dag: &mut TermDag,
    func_name: &str,
    prog: &[ResolvedNCommand],
    globals: &HashMap<String, TermId>,
    old_term: TermId,
    new_term: TermId,
    idx: usize,
) -> Result<(TermId, HashSet<Proposition>), ProofCheckError> {
    for cmd in prog {
        if let GenericNCommand::Function(func_decl) = cmd
            && func_decl.name == func_name
        {
            let merge = func_decl.merge.as_ref().ok_or_else(|| {
                ProofCheckError::from(ProofCheckErrorKind::FunctionNotFound {
                    function_name: func_name.to_string(),
                })
            })?;
            let subexpr = subexpr_at_index(&merge.result, idx).ok_or_else(|| {
                ProofCheckError::from(ProofCheckErrorKind::FunctionNotFound {
                    function_name: format!("{func_name} (merge subexpr index {idx} out of range)"),
                })
            })?;
            return eval_merge_expr(term_dag, subexpr, globals, old_term, new_term);
        }
    }
    Err(ProofCheckErrorKind::FunctionNotFound {
        function_name: func_name.to_string(),
    }
    .into())
}

/// True iff `fact` is a custom-function application fact `(= (f args) v)`, for
/// which the checker's proof normal form expects a *reflexive* premise proof.
/// Constructor and plain equality facts are excluded. Proof normal form always
/// writes the call on the left (see [`crate::proofs::proof_normal_form`]).
fn is_custom_func_fact(fact: &ResolvedFact) -> bool {
    let call = match fact {
        ResolvedFact::Eq(_, ResolvedExpr::Call(_, c, _), ResolvedExpr::Var(..)) => c,
        _ => return false,
    };
    matches!(call, ResolvedCall::Func(ft) if ft.subtype == FunctionSubtype::Custom)
}

/// Evaluate top-level let definitions in declaration order.
pub(in crate::proofs) fn global_bindings(
    program: &[ResolvedNCommand],
    dag: &mut TermDag,
) -> Result<HashMap<String, TermId>, ProofCheckError> {
    let definitions: Vec<_> = program
        .iter()
        .filter(|command| {
            matches!(
                command,
                ResolvedNCommand::CoreAction(crate::GenericAction::Let(..))
            )
        })
        .cloned()
        .collect();
    crate::proofs::proof_checker::gather_globals(&definitions, dag)
}

/// Hash-consing state for one decoded proof arena, discarded after lifting.
/// The maps travel together: firing IDs occur only in this synthesis memo.
#[derive(Default)]
pub(crate) struct Synthesis {
    synthesized: HashMap<SynthKey, ProofId>,
    rule_firings: HashMap<(String, Vec<ProofId>), RuleFiringId>,
}

/// A firing's identity within one lifting arena, like the proof IDs it contains.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) struct RuleFiringId(usize);

/// What a synthesized proof is, for sharing one node per distinct value.
#[derive(Clone, PartialEq, Eq, Hash)]
pub(crate) enum SynthKey {
    /// A rule head's own conclusion: its interned firing and proof column.
    Rule(RuleFiringId, i64),
    Sym(ProofId),
    Trans(ProofId, ProofId),
    Congr(ProofId, usize, ProofId),
    /// A positional projection from an existing proof.
    Proj(ProofId, usize),
    /// A premise the encoding stored no row for (see
    /// [`crate::proofs::proof_encoding_helpers::recomputable_premises`]).
    Fiat(TermId, TermId),
}

/// Pair one proof arena with its temporary construction memo. Recursive bridge
/// lifting receives this same pair; neither memo nor compact IDs enter proofs.
pub(crate) struct ProofBuilder<'a> {
    pub(super) store: &'a mut ProofStore,
    pub(super) synthesis: &'a mut Synthesis,
}

impl ProofBuilder<'_> {
    /// Add a proof, sharing one node per distinct `key`. The e-graph
    /// hash-conses its own proof rows, so proofs reconstructed during lifting
    /// must be shared too — otherwise a subproof reached along several paths
    /// becomes a fresh copy per path, and the proof unfolds into a tree.
    pub(super) fn push_shared_proof(&mut self, key: SynthKey, proof: Proof) -> ProofId {
        match self.synthesis.synthesized.entry(key) {
            HEntry::Occupied(entry) => *entry.get(),
            HEntry::Vacant(entry) => {
                let id = self.store.id_to_proof.push(proof);
                entry.insert(id);
                id
            }
        }
    }

    /// Intern the old structural rule key once for all columns of a firing.
    /// Names compare by string contents and premises by their order and IDs.
    pub(super) fn rule_firing(&mut self, name: &str, premises: &[ProofId]) -> RuleFiringId {
        let next = RuleFiringId(self.synthesis.rule_firings.len());
        *self
            .synthesis
            .rule_firings
            .entry((name.to_owned(), premises.to_vec()))
            .or_insert(next)
    }

    /// Construct a positional projection, sharing it with every projection
    /// from the same proof and child index.
    pub(super) fn push_projection(&mut self, proof: ProofId, child_index: usize) -> ProofId {
        let child = self
            .store
            .term_child(self.store.id_to_proof[proof].rhs(), child_index);
        self.push_shared_proof(
            SynthKey::Proj(proof, child_index),
            Proof {
                proposition: Proposition::new(child, child),
                justification: Justification::Proj { proof, child_index },
            },
        )
    }

    /// The reflexive fiat a [`recomputable_premises`] fact's premise is, over the
    /// base value the fact evaluates to under `substitution`. Shared, so the rows
    /// of one firing name the same premise.
    fn recomputed_premise(
        &mut self,
        rule_name: &str,
        fact: &ResolvedFact,
        substitution: &IndexMap<String, TermId>,
    ) -> ProofId {
        let bindings: HashMap<String, TermId> = substitution
            .iter()
            .map(|(var, term)| (var.clone(), *term))
            .collect();
        let eval = |store: &mut Self, expr: &ResolvedExpr| {
            eval_expr_with_subst(rule_name, expr, &mut store.store.term_dag, &bindings)
                .ok()
                .map(|(term, _props)| term)
        };
        let (lhs, rhs) = match fact {
            ResolvedFact::Fact(expr) => {
                let term = eval(self, expr).unwrap_or_else(|| {
                    panic!("rule {rule_name}: premise-free fact {fact} does not evaluate")
                });
                (term, term)
            }
            // Only one side need evaluate: the other is a variable this premise
            // binds, so it states the same term.
            ResolvedFact::Eq(_, lhs, rhs) => match (eval(self, lhs), eval(self, rhs)) {
                (Some(lhs), Some(rhs)) => (lhs, rhs),
                (Some(term), None) | (None, Some(term)) => (term, term),
                (None, None) => {
                    panic!("rule {rule_name}: premise-free fact {fact} has no evaluable side")
                }
            },
        };
        self.push_shared_proof(
            SynthKey::Fiat(lhs, rhs),
            Proof {
                proposition: Proposition::new(lhs, rhs),
                justification: Justification::Fiat,
            },
        )
    }
}

pub(super) struct ProofLifter<'a> {
    program: &'a [ResolvedNCommand],
    globals: &'a HashMap<String, TermId>,
    raw: &'a RawProofStore,
    proof_id: &'a mut DenseIdMap<RawProofId, ProofId>,
    rules: HashMap<&'a str, &'a ResolvedRule>,
    actions: Vec<&'a crate::ast::ResolvedAction>,
    head_plans: HashMap<String, Rc<HeadPlan>>,
    action_plans: HashMap<usize, Rc<HeadPlan>>,
    /// The furthest replay of each firing, shared by all its proof columns.
    head_walks: HashMap<(String, Vec<ProofId>), HeadWalk>,
}

impl<'a> ProofLifter<'a> {
    pub(super) fn new(
        program: &'a [ResolvedNCommand],
        globals: &'a HashMap<String, TermId>,
        raw: &'a RawProofStore,
        proof_id: &'a mut DenseIdMap<RawProofId, ProofId>,
    ) -> Self {
        let mut rules = HashMap::default();
        for command in program {
            if let ResolvedNCommand::NormRule { rule } = command {
                rules.entry(rule.name.as_str()).or_insert(rule);
            }
        }
        Self {
            program,
            globals,
            raw,
            proof_id,
            rules,
            actions: crate::proofs::proof_checker::gather_global_actions(program).collect(),
            head_plans: HashMap::default(),
            action_plans: HashMap::default(),
            head_walks: HashMap::default(),
        }
    }

    fn action(&self, at: usize) -> &'a crate::ast::ResolvedAction {
        self.actions.get(at).copied().unwrap_or_else(|| {
            panic!(
                "a fiat names global action {at}, but the program has {}",
                self.actions.len()
            )
        })
    }

    fn action_plan(&mut self, at: usize) -> Rc<HeadPlan> {
        if let Some(plan) = self.action_plans.get(&at) {
            return plan.clone();
        }
        // The encoder numbers the planned action. Reproduce that layout once;
        // the generated local names affect only the plan, never the proof.
        let mut next = 0usize;
        let mut fresh = || {
            next += 1;
            format!("@plan{next}")
        };
        let plan = Rc::new(HeadPlan::new(
            std::slice::from_ref(self.action(at)),
            &mut fresh,
        ));
        self.action_plans.insert(at, plan.clone());
        plan
    }

    /// The term a rule body's element read produces and the resolved signature's
    /// unique argument capable of holding it: the primitive at `body_index` of
    /// `rule`'s body, run on `arg_terms` through the same validator the checker
    /// uses when it re-evaluates a body.
    fn run_body_primitive(
        &mut self,
        store: &mut ProofBuilder<'_>,
        rule: &str,
        body_index: usize,
        arg_terms: &[TermId],
    ) -> (TermId, usize) {
        let resolved = self.rule_named(rule);
        let body = crate::proofs::proof_encoding_helpers::body_exprs(&resolved.body);
        let expr = body
            .get(body_index)
            .unwrap_or_else(|| panic!("rule {rule} has no body node {body_index}"));
        let ResolvedExpr::Call(_, ResolvedCall::Primitive(prim), _) = expr else {
            panic!("body node {body_index} of rule {rule} is not a primitive call");
        };
        let typed_container_index = prim
            .input()
            .iter()
            .position(|sort| holds_sort(sort, prim.output().name()))
            .expect("proof support should have found one container for a primitive projection");
        let validator = prim
            .validator()
            .unwrap_or_else(|| {
                panic!(
                    "primitive {} has no validator; proof support gates this",
                    prim.name()
                )
            })
            .clone();
        let element = validator(&mut store.store.term_dag, arg_terms).unwrap_or_else(|| {
            panic!(
                "validator for {} rejected the argument terms of body node {body_index} in rule {rule}",
                prim.name()
            )
        });
        (element, typed_container_index)
    }

    /// The equality the `at`th global action of `prog` states, oriented the way
    /// the encoding wrote it.
    ///
    /// A top-level `union`'s fiat names the action instead of its endpoints, so
    /// they are recovered by evaluating the action's two operands — under the
    /// global bindings, since an operand may name a global.
    fn union_endpoints(
        &mut self,
        store: &mut ProofBuilder<'_>,
        at: usize,
        swapped: bool,
    ) -> (TermId, TermId) {
        let action = self.action(at);
        let crate::GenericAction::Union(_, lhs, rhs) = action else {
            panic!("a fiat names global action {at} as a union, but it is not one");
        };
        let (lhs, rhs) = (
            self.eval_global(store, at, lhs),
            self.eval_global(store, at, rhs),
        );
        if swapped { (rhs, lhs) } else { (lhs, rhs) }
    }

    /// The term written at node `node` of the `at`th global action of `prog`.
    ///
    /// A reflexive fiat names that position instead of the term, so the term is
    /// recovered by evaluating the node — under the global bindings, since it
    /// may name a global.
    fn action_term(&mut self, store: &mut ProofBuilder<'_>, at: usize, node: usize) -> TermId {
        let plan = self.action_plan(at);
        use crate::proofs::proof_encoding_helpers::{ActionNode, action_nodes};
        let nodes: Vec<ActionNode<'_>> = plan.actions.iter().flat_map(action_nodes).collect();
        match nodes.get(node) {
            Some(ActionNode::Expr(expr)) => self.eval_global(store, at, expr),
            // The row a `set` writes is the application of the function to its
            // arguments and the value, which no expression of the action denotes.
            Some(ActionNode::Row(crate::GenericAction::Set(_, head, args, value))) => {
                let mut children: Vec<TermId> = args
                    .iter()
                    .map(|arg| self.eval_global(store, at, arg))
                    .collect();
                children.push(self.eval_global(store, at, value));
                store.store.term_dag.app(head.name().to_string(), children)
            }
            Some(ActionNode::Row(other)) => panic!("{other} writes no row"),
            None => panic!(
                "a fiat names node {node} of global action {at}, which has {} nodes",
                nodes.len()
            ),
        }
    }

    /// Evaluate `expr`, written in the `at`th global action, under the global
    /// bindings — an expression a fiat names may itself name a global.
    fn eval_global(
        &mut self,
        store: &mut ProofBuilder<'_>,
        at: usize,
        expr: &crate::ast::ResolvedExpr,
    ) -> TermId {
        crate::proofs::proof_checker::eval_expr_with_subst(
            "global_action",
            expr,
            &mut store.store.term_dag,
            self.globals,
        )
        .unwrap_or_else(|err| panic!("could not evaluate global action {at}: {err}"))
        .0
    }

    /// Reflexivize a (possibly non-reflexive) proof for use where the checker
    /// requires a reflexive premise (`lhs == rhs`), e.g. a `MergeFn` premise. For
    /// `p : A = B` returns a proof of `B = B` as `Trans(Sym(p), p)`; an already-
    /// reflexive `p` is returned unchanged.
    ///
    /// This handles eq-sort inputs to FD custom functions: rebuild rewrites the
    /// view row's proof into a congruence proof `f(orig) = f(canon)`, and
    /// reflexivizing to its RHS lands both premises on the same canonical view row
    /// so the checker's input-match succeeds.
    fn reflexivize_premise(
        &mut self,
        store: &mut ProofBuilder<'_>,
        premise_id: ProofId,
    ) -> ProofId {
        let prop = &store.store.id_to_proof[premise_id].proposition;
        if prop.lhs == prop.rhs {
            return premise_id;
        }
        // Shared, so the two rows of one firing reflexivize a premise to the
        // same id: the premise vector is both the walk memo's key and the
        // rule proofs' sharing key.
        store.reflexive(premise_id)
    }

    /// The two `MergeFn*` premise proofs end (rhs) at the colliding view terms
    /// `f(inputs.., output)`. Extract the view head, the shared input args,
    /// and the two output values from the premises' rhs (read before reflexivizing).
    fn merge_premise_view(
        &self,
        store: &ProofBuilder<'_>,
        old_proof_id: ProofId,
        new_proof_id: ProofId,
    ) -> (String, Vec<TermId>, TermId, TermId) {
        let old_view = store.store.id_to_proof[old_proof_id].rhs();
        let new_view = store.store.id_to_proof[new_proof_id].rhs();
        match (
            store.store.term_dag.get(old_view),
            store.store.term_dag.get(new_view),
        ) {
            (Term::App(old_head, old_args), Term::App(_new_head, new_args)) => {
                let head = old_head.clone();
                let old_output = *old_args.last().expect("merge view term has no args");
                let new_output = *new_args.last().expect("merge view term has no args");
                let inputs = old_args[..old_args.len() - 1].to_vec();
                (head, inputs, old_output, new_output)
            }
            _ => panic!(
                "MergeFn premise proofs should prove function application terms, got {:?} and {:?}",
                store.store.term_dag.get(old_view),
                store.store.term_dag.get(new_view)
            ),
        }
    }

    /// Build a `MergeFn` proof of `to_prove = to_prove` from the two premises,
    /// reflexivizing each ([`Self::reflexivize_premise`]).
    fn merge_fn_proof(
        &mut self,
        store: &mut ProofBuilder<'_>,
        function: &str,
        old_proof_id: ProofId,
        new_proof_id: ProofId,
        to_prove: TermId,
    ) -> Proof {
        let old_proof = self.reflexivize_premise(store, old_proof_id);
        let new_proof = self.reflexivize_premise(store, new_proof_id);
        Proof {
            proposition: Proposition::new(to_prove, to_prove),
            justification: Justification::MergeFn {
                function: function.to_string(),
                old_proof,
                new_proof,
            },
        }
    }

    /// Lift a recorded proof to source statements with instantiated rule premises.
    ///
    /// Panics if the raw proof is invalid with respect to the program.
    pub(super) fn proof(
        &mut self,
        store: &mut ProofBuilder<'_>,
        raw_proof_id: RawProofId,
    ) -> ProofId {
        let raw_store = self.raw;
        let prog = self.program;
        let globals = self.globals;
        if let Some(&id) = self.proof_id.get(raw_proof_id) {
            return id;
        }
        let raw_proof = raw_store.get(raw_proof_id);

        let proof = match raw_proof {
            RawProof::FiatUnion(at, swapped) => {
                let (lhs, rhs) = self.union_endpoints(store, *at, *swapped);
                Proof {
                    proposition: Proposition::new(lhs, rhs),
                    justification: Justification::Fiat,
                }
            }
            RawProof::FiatTerm(at, node) => {
                let term = self.action_term(store, *at, *node);
                Proof {
                    proposition: Proposition::new(term, term),
                    justification: Justification::Fiat,
                }
            }
            RawProof::Fiat(lhs, rhs) => Proof {
                proposition: Proposition::new(*lhs, *rhs),
                justification: Justification::Fiat,
            },
            RawProof::Rule(name, premise_proofs, bridge_proofs, raw_column) => {
                let rule = self.rule_named(name);
                let planned = self.head_plan(rule);
                let (lifted_premises, substitution) =
                    self.rule_premises(store, name, rule, premise_proofs);

                // This row carries on the walk the last row of the same firing
                // left off at. A row reached while this one walks starts its own,
                // so the further of the two is the one kept.
                let firing_key = (name.clone(), lifted_premises.clone());
                let carried = self.head_walks.remove(&firing_key);
                // A carried walk brings the bindings the earlier row seeded it
                // with, so only a walk starting from scratch needs them.
                let bindings = match &carried {
                    Some(_) => HashMap::default(),
                    None => {
                        // Each continuation retains its bindings while lifting.
                        // Keep only the globals this head reads, rather than
                        // copying every program global into every firing.
                        let mut bindings = HashMap::default();
                        rule.head.visit_vars(&mut |_, var| {
                            if let Some(&term) = globals.get(&var.name) {
                                bindings.insert(var.name.clone(), term);
                            }
                        });
                        bindings
                            .extend(substitution.iter().map(|(var, term)| (var.clone(), *term)));
                        bindings
                    }
                };
                // A global's value is in every substitution, so recording it in the
                // proof would only repeat the program.
                let mut recorded = substitution;
                recorded.retain(|var, _term| globals.get(var).is_none());
                // The bridges are in the order the head builds, which is the
                // order the walk takes them in, so the supply picks up where the
                // carried walk stopped.
                let mut next = carried.as_ref().map_or(0, HeadWalk::bridges_taken);
                let mut firing = Firing::new(
                    name,
                    &planned,
                    bindings,
                    lifted_premises,
                    recorded,
                    Box::new(|store: &mut ProofBuilder<'_>, _to_canonical| {
                        let raw = *bridge_proofs.get(next)?;
                        next += 1;
                        Some(self.proof(store, raw))
                    }),
                );
                if let Some(walk) = carried {
                    firing.carry_on(walk);
                }
                let proof_id = firing.column(store, *raw_column);
                let walked = firing.into_walk();
                let further = self
                    .head_walks
                    .get(&firing_key)
                    .is_none_or(|kept| kept.reaches() < walked.reaches());
                if further {
                    self.head_walks.insert(firing_key, walked);
                }
                self.proof_id.insert(raw_proof_id, proof_id);
                return proof_id;
            }
            RawProof::MergeFnIdx(function, old_raw, new_raw, idx) => {
                let old_proof_id = self.proof(store, *old_raw);
                let new_proof_id = self.proof(store, *new_raw);
                // `idx` indexes all body nodes (pre-order, top node included). The
                // conclusion is that node's own minted term, i.e. its existence proof in
                // its FD view. The whole-view-row conclusion comes from `MergeFnRow`.
                let (_head, _inputs, old_output, new_output) =
                    self.merge_premise_view(store, old_proof_id, new_proof_id);
                let (to_prove, _props) = run_merge_subexpr(
                    &mut store.store.term_dag,
                    function,
                    prog,
                    globals,
                    old_output,
                    new_output,
                    *idx,
                )
                .unwrap_or_else(|e| {
                    panic!("failed to run merge subexpr {idx} for {function}: {e}")
                });
                self.merge_fn_proof(store, function, old_proof_id, new_proof_id, to_prove)
            }
            RawProof::MergeFnRow(function, old_raw, new_raw) => {
                let old_proof_id = self.proof(store, *old_raw);
                let new_proof_id = self.proof(store, *new_raw);
                // The conclusion is the whole view row `f(inputs..., merged)`, where
                // `merged` is the whole merge body evaluated on the two premise outputs.
                let (view_head, input_args, old_output, new_output) =
                    self.merge_premise_view(store, old_proof_id, new_proof_id);
                let (merged_child, _props) = run_merge(
                    &mut store.store.term_dag,
                    function,
                    prog,
                    globals,
                    old_output,
                    new_output,
                )
                .unwrap_or_else(|e| panic!("failed to run merge for {function}: {e}"));
                let mut merged_args = input_args;
                merged_args.push(merged_child);
                let to_prove = store.store.term_dag.app(view_head, merged_args);
                self.merge_fn_proof(store, function, old_proof_id, new_proof_id, to_prove)
            }
            RawProof::Trans(left_raw, right_raw) => {
                let left_id = self.proof(store, *left_raw);
                let right_id = self.proof(store, *right_raw);
                let left = &store.store.id_to_proof[left_id];
                let right = &store.store.id_to_proof[right_id];
                assert_eq!(
                    left.rhs(),
                    right.lhs(),
                    "transitivity requires matching middle terms"
                );
                Proof {
                    proposition: Proposition::new(left.lhs(), right.rhs()),
                    justification: Justification::Trans(left_id, right_id),
                }
            }
            RawProof::Sym(inner_raw) => {
                let inner_id = self.proof(store, *inner_raw);
                let inner = &store.store.id_to_proof[inner_id];
                Proof {
                    proposition: Proposition::new(inner.rhs(), inner.lhs()),
                    justification: Justification::Sym(inner_id),
                }
            }
            RawProof::Congr(proof_raw, child_index, child_raw) => {
                let base_id = self.proof(store, *proof_raw);
                let child_id = self.proof(store, *child_raw);
                let base_lhs = store.store.id_to_proof[base_id].lhs();
                let base_rhs = store.store.id_to_proof[base_id].rhs();
                let child_rhs = store.store.id_to_proof[child_id].rhs();
                store
                    .store
                    .assert_congr_starts_at_child(base_rhs, *child_index, child_id);
                let rhs = store
                    .store
                    .replace_term_child(base_rhs, *child_index, child_rhs);

                Proof {
                    proposition: Proposition::new(base_lhs, rhs),
                    justification: Justification::Congr {
                        proof: base_id,
                        child_index: *child_index,
                        child_proof: child_id,
                    },
                }
            }
            RawProof::Proj(inner_raw, child_index) => {
                let inner_id = self.proof(store, *inner_raw);
                let projected = store.push_projection(inner_id, *child_index);
                self.proof_id.insert(raw_proof_id, projected);
                return projected;
            }
            RawProof::ProjPrim(rule, body_index, arg_raws) => {
                let arg_ids: Vec<ProofId> =
                    arg_raws.iter().map(|arg| self.proof(store, *arg)).collect();
                let arg_terms: Vec<TermId> = arg_ids
                    .iter()
                    .map(|id| store.store.id_to_proof[*id].rhs())
                    .collect();
                // The resolved call, not just the primitive's name: egglog
                // overloads names across sorts, and only the resolved call fixes
                // which validator states what the read means on terms.
                let (element, container_index) =
                    self.run_body_primitive(store, rule, *body_index, &arg_terms);
                // The resolved signature identifies the one argument whose sort
                // can hold the result. An unrelated argument term may contain the
                // same child, so term occurrence alone is not provenance.
                let container_id = arg_ids[container_index];
                let container_term = arg_terms[container_index];
                let path = store
                    .store
                    .projection_path_to_descendant(container_term, element)
                    .unwrap_or_else(|| {
                        panic!(
                            "primitive projection: body node {body_index} of rule {rule} read \
                             {} out of no descendant of container argument {container_index}",
                            store.store.term_dag.to_string(element)
                        )
                    });
                let mut projected = container_id;
                for child_index in path {
                    projected = store.push_projection(projected, child_index);
                }
                self.proof_id.insert(raw_proof_id, projected);
                return projected;
            }
            RawProof::CongrAll(proof_raw, child_raw) => {
                let base_id = self.proof(store, *proof_raw);
                let child_id = self.proof(store, *child_raw);
                let expanded_id = store.store.expand_congr_all(base_id, child_id);
                self.proof_id.insert(raw_proof_id, expanded_id);
                return expanded_id;
            }
            RawProof::ContainerNormalize(inner_raw) => {
                let inner_id = self.proof(store, *inner_raw);
                let inner_lhs = store.store.id_to_proof[inner_id].lhs();
                let inner_rhs = store.store.id_to_proof[inner_id].rhs();
                let normalized = store.store.normalize_container(inner_rhs);
                Proof {
                    proposition: Proposition::new(inner_lhs, normalized),
                    justification: Justification::ContainerNormalize { proof: inner_id },
                }
            }
            RawProof::Eval => {
                // The marker proves nothing on its own; `check_side_condition`
                // re-evaluates the side condition against the rule body. Give it
                // a placeholder proposition (the `Proof` struct requires one).
                let placeholder = store
                    .store
                    .term_dag
                    .app("@side-condition".to_string(), vec![]);
                Proof {
                    proposition: Proposition::new(placeholder, placeholder),
                    justification: Justification::Eval,
                }
            }
        };

        let proof_id = store.store.id_to_proof.push(proof);
        self.proof_id.insert(raw_proof_id, proof_id);
        proof_id
    }

    pub(super) fn visit_origins(&self, store: &ProofBuilder<'_>, visit: &mut ProofVisitor<'_>) {
        let mut globals: Vec<_> = self
            .raw
            .proofs()
            .filter_map(|(raw_id, raw)| {
                let proof = *self.proof_id.get(raw_id)?;
                match raw {
                    RawProof::FiatTerm(action, node) => Some((*action, Some(*node), false, proof)),
                    RawProof::FiatUnion(action, swapped) => Some((*action, None, *swapped, proof)),
                    _ => None,
                }
            })
            .collect();
        globals.sort_unstable_by_key(|(action, node, swapped, _)| {
            (*action, node.unwrap_or(usize::MAX), *swapped)
        });
        for action in globals.chunk_by(|a, b| a.0 == b.0) {
            let ordinal = action[0].0;
            let mut terms = action
                .iter()
                .filter(|(_, node, _, _)| node.is_some())
                .peekable();
            let mut next = 0;
            crate::proofs::proof_head::visit_normalized_action(
                self.action(ordinal),
                &mut || "@origin".into(),
                &mut |operand, action| {
                    crate::proofs::proof_encoding_helpers::visit_action_nodes(
                        &action,
                        &mut |_, path| {
                            while terms
                                .peek()
                                .is_some_and(|(_, node, _, _)| *node == Some(next))
                            {
                                let (_, _, _, proof) = terms.next().unwrap();
                                let mut path = path.to_vec();
                                if let Some(operand) = operand {
                                    path[0] = operand;
                                }
                                visit(
                                    store.store,
                                    *proof,
                                    ProofOrigin::GlobalTerm {
                                        program: self.program,
                                        action: ordinal,
                                        path: &path,
                                    },
                                );
                            }
                            next += 1;
                        },
                    );
                },
            );
            assert!(terms.next().is_none(), "the action term was evaluated");
            for &(_, node, swapped, proof) in action {
                if node.is_none() {
                    visit(
                        store.store,
                        proof,
                        ProofOrigin::GlobalUnion {
                            program: self.program,
                            action: ordinal,
                            swapped,
                        },
                    );
                }
            }
        }
        let mut conclusions = Vec::new();
        // A recursive bridge may have completed a different continuation of a
        // firing. The synthesis memo retains every own conclusion, including
        // columns absent from the single continuation kept for further replay.
        for (key, &proof) in &store.synthesis.synthesized {
            if let SynthKey::Rule(_, column) = key {
                let Justification::Rule { name, .. } = store.store.get(proof).justification()
                else {
                    unreachable!("an own rule conclusion has a rule justification");
                };
                conclusions.push((proof, self.rule_named(name), *column as usize));
            }
        }
        conclusions.sort_unstable_by_key(|(proof, _, _)| *proof);
        conclusions.dedup_by_key(|(proof, _, _)| *proof);
        for (proof, rule, column) in conclusions {
            let (action, path) = self.head_plans[&rule.name].source_position(column, &rule.head.0);
            visit(
                store.store,
                proof,
                ProofOrigin::Rule {
                    program: self.program,
                    rule,
                    action,
                    path: &path,
                },
            );
        }
    }

    /// The rule the proof names, which the encoder guarantees is in the program.
    fn rule_named(&self, rule_name: &str) -> &'a ResolvedRule {
        self.rules
            .get(rule_name)
            .copied()
            .unwrap_or_else(|| panic!("could not find rule with name {rule_name}"))
    }

    /// The lowering plan for `rule`'s head.
    fn head_plan(&mut self, rule: &ResolvedRule) -> Rc<HeadPlan> {
        if let Some(plan) = self.head_plans.get(&rule.name) {
            return plan.clone();
        }
        let mut minted = 0usize;
        let mut fresh = || {
            minted += 1;
            format!("@union-operand-{minted}")
        };
        let plan = Rc::new(HeadPlan::new(&rule.head.0, &mut fresh));
        self.head_plans.insert(rule.name.clone(), plan.clone());
        plan
    }

    /// A firing's premise proof per body fact, and the substitution they fix.
    /// Substitution entries come out in the order the variables first occur in
    /// the rule body.
    ///
    /// The encoding stores no row for a [`recomputable_premises`] fact, so that
    /// premise is rebuilt by evaluating the fact against the bindings the earlier
    /// facts gave. `premise_proofs` holds the stored rows only, in body order;
    /// any trailing ones are the lookups `remove_globals` appended for the
    /// globals the head mentions, which `prog`'s rule predates, so they are left
    /// unread.
    fn rule_premises(
        &mut self,
        store: &mut ProofBuilder<'_>,
        name: &str,
        rule: &ResolvedRule,
        premise_proofs: &[RawProofId],
    ) -> (Vec<ProofId>, IndexMap<String, TermId>) {
        let globals = self.globals;
        let recomputable = recomputable_premises(&rule.body, &|var| globals.contains_key(var));
        let mut stored = premise_proofs.iter();
        let mut substitution = IndexMap::default();
        let mut lifted = Vec::with_capacity(rule.body.len());
        for (fact, recomputable) in rule.body.iter().zip(recomputable) {
            let premise = if recomputable {
                store.recomputed_premise(name, fact, &substitution)
            } else {
                let raw = *stored.next().unwrap_or_else(|| {
                    panic!(
                        "rule {name} recorded {} premises for a body of {} facts",
                        premise_proofs.len(),
                        rule.body.len()
                    )
                });
                let premise = self.proof(store, raw);
                // Rebuild/canonicalization can rewrite a matched custom-function-fact
                // premise `(= (f args) v)` into a non-reflexive natural->canonical
                // `Congr` proof `(f nat) = (f canon)` (e.g. when an argument's e-class
                // has several equivalent shapes from commutativity/associativity
                // rewrites). The checker's function-fact normal form expects a
                // reflexive premise at the matched (canonical) shape, so reflexivize
                // those. Equality-fact premises `(= a b)` must stay non-reflexive.
                if is_custom_func_fact(fact) {
                    self.reflexivize_premise(store, premise)
                } else {
                    premise
                }
            };
            // Container side conditions carry only an `Eval` marker (no value);
            // their bindings are generated by `check_side_condition` at check
            // time, so there is nothing to unify here.
            if !crate::proofs::proof_checker::is_container_side_condition(fact) {
                store.store.unify_fact(fact, premise, &mut substitution);
            }
            lifted.push(premise);
        }
        (lifted, substitution)
    }
}

impl ProofStore {
    /// Lift recorded proof nodes, resolving globals from the source bindings.
    fn lift(
        prog: &[ResolvedNCommand],
        raw_store: &RawProofStore,
        raw_proof_ids: &[RawProofId],
        container_normalizers: HashMap<String, PrimitiveValidator>,
        prim_value_constructors: HashSet<String>,
        visit: Option<&mut ProofVisitor<'_>>,
    ) -> (ProofStore, Vec<ProofId>) {
        let mut store = ProofStore::new(
            raw_store.term_dag.clone(),
            container_normalizers,
            prim_value_constructors,
        );
        let globals = global_bindings(prog, &mut store.term_dag)
            .unwrap_or_else(|_| panic!("failed to gather globals from program"));

        let mut synthesis = Synthesis::default();
        let mut builder = ProofBuilder {
            store: &mut store,
            synthesis: &mut synthesis,
        };
        let mut proof_ids = DenseIdMap::new();
        let mut lifting = ProofLifter::new(prog, &globals, raw_store, &mut proof_ids);
        let roots = raw_proof_ids
            .iter()
            .map(|&root| lifting.proof(&mut builder, root))
            .collect();
        if let Some(visit) = visit {
            lifting.visit_origins(&builder, visit);
        }
        (store, roots)
    }

    /// Bind the fact's variables from the term its premise proof proves. A
    /// primitive call contributes no bindings of its own — the value it computes
    /// is read off the proof instead.
    fn unify_fact(
        &self,
        fact: &ResolvedFact,
        proof_id: ProofId,
        subst: &mut IndexMap<String, TermId>,
    ) {
        let proof = &self.id_to_proof[proof_id];
        match fact {
            // In proof normal form, this is the only way that function calls apppear.
            ResolvedFact::Eq(
                _span,
                ResolvedExpr::Call(_span2, head @ ResolvedCall::Func(_), args),
                ResolvedExpr::Var(_span3, v),
            ) if head.is_custom_func() => {
                let term = proof.rhs();
                let children = match self.term_dag.get(term) {
                    Term::App(head_name, children) if head_name == head.name() => children.clone(),
                    _ => panic!("expected function application term in proof rhs"),
                };
                // assert children length matches args length + 1 for bound var
                if children.len() != args.len() + 1 {
                    panic!(
                        "function call arity mismatch for {}: expected {}, got {}",
                        head.name(),
                        args.len() + 1,
                        children.len()
                    );
                }

                // unify the arguments before binding v to the last child, so the
                // substitution records the variables in the order the fact writes them
                for (arg_expr, child_term) in args.iter().zip(children.iter()) {
                    self.unify_expr(arg_expr, *child_term, subst);
                }
                let var_child_term = children.last().unwrap();
                self.add_to_subst(subst, &v.name, *var_child_term);
            }
            ResolvedFact::Eq(_, lhs_expr, rhs_expr) => {
                self.unify_expr(lhs_expr, proof.lhs(), subst);
                self.unify_expr(rhs_expr, proof.rhs(), subst);
            }
            ResolvedFact::Fact(expr) => {
                self.unify_expr(expr, proof.rhs(), subst);
            }
        }
    }

    fn add_to_subst(&self, subst: &mut IndexMap<String, TermId>, var: &str, term_id: TermId) {
        match subst.entry(var.to_string()) {
            IEntry::Vacant(entry) => {
                entry.insert(term_id);
            }
            IEntry::Occupied(entry) => {
                if *entry.get() != term_id {
                    panic!(
                        "conflicting substitutions for variable {}: {:?} vs {:?}",
                        var,
                        self.term_dag.get(*entry.get()),
                        self.term_dag.get(term_id)
                    );
                }
            }
        }
    }

    fn unify_expr(
        &self,
        expr: &ResolvedExpr,
        term_id: TermId,
        substitution: &mut IndexMap<String, TermId>,
    ) {
        match expr {
            ResolvedExpr::Lit(_, _lit) => (),
            ResolvedExpr::Var(_, var) => {
                self.add_to_subst(substitution, &var.name, term_id);
            }
            ResolvedExpr::Call(_, call, args) => {
                // if the call is a primitive we don't need to do anything
                // because proofs don't support primitves with children applications that are not primitives
                if let ResolvedCall::Primitive(_) = call {
                    return;
                }
                let Term::App(head, children) = self.term_dag.get(term_id) else {
                    panic!(
                        "expected function application term for call {}, got {:?}. Lifting from raw proofs assumes valid proofs with respect to the program.",
                        call.name(),
                        self.term_dag.get(term_id)
                    );
                };
                if head != call.name() {
                    panic!(
                        "function call head mismatch: expected {}, got {head}",
                        call.name(),
                    );
                }

                if children.len() != args.len() {
                    panic!(
                        "function call arity mismatch for {}: expected {}, got {}",
                        call.name(),
                        args.len(),
                        children.len()
                    );
                }
                for (arg_expr, child_term) in args.iter().zip(children.iter()) {
                    self.unify_expr(arg_expr, *child_term, substitution);
                }
            }
        }
    }

    /// Expand an element-matching congruence ([`RawProof::CongrAll`]) into a
    /// chain of positional [`Justification::Congr`] steps, one per child of
    /// the base proof's rhs equal to the child proof's lhs, so the user-facing
    /// proof needs no new justification kind.
    ///
    /// A `CongrAll` may be the identity at the term level, expanding to zero
    /// steps: distinct element *values* can share one term shape (a natural id
    /// and its dedup id), so the child proof's endpoints may coincide, and a
    /// prior `CongrAll` whose lhs is that shared term already rewrote every
    /// occurrence.
    fn expand_congr_all(&mut self, base_id: ProofId, child_id: ProofId) -> ProofId {
        let child_lhs = self.id_to_proof[child_id].lhs();
        let child_rhs = self.id_to_proof[child_id].rhs();
        let mut current = base_id;
        if child_lhs == child_rhs {
            return current;
        }
        current = self.congr_all_direct(current, child_id, child_lhs, child_rhs);
        self.congr_all_nested(current, child_id)
    }

    /// Whether `term` is an application with a registered container normalizer.
    fn is_container_term(&self, term: TermId) -> bool {
        matches!(self.term_dag.get(term), Term::App(head, _)
            if self.container_normalizers.contains_key(head))
    }

    /// Rewrite `child_lhs` to `child_rhs` at every direct child of `current`'s
    /// right-hand side.
    fn congr_all_direct(
        &mut self,
        base_id: ProofId,
        child_id: ProofId,
        child_lhs: TermId,
        child_rhs: TermId,
    ) -> ProofId {
        let mut current = base_id;
        loop {
            let lhs = self.id_to_proof[current].lhs();
            let rhs = self.id_to_proof[current].rhs();
            let Term::App(_, children) = self.term_dag.get(rhs) else {
                panic!("congr-all requires an application term. Lifting assumes valid proofs.");
            };
            let Some(child_index) = children.iter().position(|c| *c == child_lhs) else {
                break;
            };
            let new_rhs = self.replace_term_child(rhs, child_index, child_rhs);
            current = self.id_to_proof.push(Proof {
                proposition: Proposition::new(lhs, new_rhs),
                justification: Justification::Congr {
                    proof: current,
                    child_index,
                    child_proof: child_id,
                },
            });
        }
        current
    }

    /// Rewrite inside every container child of `current`'s right-hand side, then
    /// canonicalize that child and congruence it back into its parent.
    ///
    /// Recurses through containers and stops at eq-sort elements, matching what
    /// the value rebuild does (see `rebuild_container_value_rec`). A child's
    /// canonical form fixes its parent's element order, so it is normalized
    /// before the step that puts it back.
    fn congr_all_nested(&mut self, base_id: ProofId, child_id: ProofId) -> ProofId {
        let mut current = base_id;
        let mut child_index = 0;
        loop {
            let rhs = self.id_to_proof[current].rhs();
            let Term::App(_, children) = self.term_dag.get(rhs) else {
                return current;
            };
            let Some(nested) = children.get(child_index).copied() else {
                return current;
            };
            child_index += 1;
            if !self.is_container_term(nested) {
                continue;
            }
            // The reflexive base the nested rewrite stands on. At lifting the
            // term is in hand, so the child's position is known here — which is
            // why the encoding needs to record none of this.
            let nested_base = self.id_to_proof.push(Proof {
                proposition: Proposition::new(nested, nested),
                justification: Justification::Proj {
                    proof: current,
                    child_index: child_index - 1,
                },
            });
            let rewritten = self.expand_congr_all(nested_base, child_id);
            let rewritten = self.normalize_step(rewritten);
            let new_nested = self.id_to_proof[rewritten].rhs();
            if new_nested == nested {
                continue;
            }
            let lhs = self.id_to_proof[current].lhs();
            let new_rhs = self.replace_term_child(rhs, child_index - 1, new_nested);
            current = self.id_to_proof.push(Proof {
                proposition: Proposition::new(lhs, new_rhs),
                justification: Justification::Congr {
                    proof: current,
                    child_index: child_index - 1,
                    child_proof: rewritten,
                },
            });
        }
    }

    /// `proof` followed by the canonicalization of its right-hand side, or
    /// `proof` unchanged when that container is already canonical.
    fn normalize_step(&mut self, proof: ProofId) -> ProofId {
        let lhs = self.id_to_proof[proof].lhs();
        let rhs = self.id_to_proof[proof].rhs();
        let normalized = self.normalize_container(rhs);
        if normalized == rhs {
            return proof;
        }
        self.id_to_proof.push(Proof {
            proposition: Proposition::new(lhs, normalized),
            justification: Justification::ContainerNormalize { proof },
        })
    }

    /// A congruence step's middle-term check, the counterpart of the one
    /// [`crate::proofs::proof_head::trans`] makes: the child the step rewrites
    /// has to be the child it starts at. Panics otherwise.
    fn assert_congr_starts_at_child(&self, base: TermId, child_index: usize, child: ProofId) {
        let child_lhs = self.id_to_proof[child].lhs();
        let base_child = match self.term_dag.get(base) {
            Term::App(_, children) => children.get(child_index).copied(),
            other => panic!("congruence requires an application term, got {other:?}"),
        };
        assert_eq!(
            base_child,
            Some(child_lhs),
            "congruence step {child_index} does not start at that child\n  base = {}\n  child lhs = {}",
            self.term_dag.to_string(base),
            self.term_dag.to_string(child_lhs),
        );
    }

    /// The projection indexes from `ancestor` to the first depth-first proper
    /// descendant equal to `target`, or `None` when no such descendant exists.
    fn projection_path_to_descendant(
        &self,
        ancestor: TermId,
        target: TermId,
    ) -> Option<Vec<usize>> {
        let mut stack = vec![(ancestor, 0)];
        let mut path = Vec::new();
        let mut visited = HashSet::default();
        visited.insert(ancestor);
        while let Some(&(term, child_index)) = stack.last() {
            let child = match self.term_dag.get(term) {
                Term::App(_, children) => children.get(child_index).copied(),
                Term::Lit(_) | Term::Var(_) => None,
            };
            let Some(child) = child else {
                stack.pop();
                path.pop();
                continue;
            };

            stack.last_mut().unwrap().1 += 1;
            path.push(child_index);
            if child == target {
                return Some(path);
            }
            if visited.insert(child) && matches!(self.term_dag.get(child), Term::App(..)) {
                stack.push((child, 0));
            } else {
                path.pop();
            }
        }
        None
    }
}

#[cfg(test)]
mod synthesis_tests {
    use super::*;
    use crate::util::IndexSet;

    #[test]
    fn rule_firing_keys_preserve_structural_sharing() {
        let mut proofs =
            ProofStore::new(TermDag::default(), HashMap::default(), HashSet::default());
        let mut synthesis = Synthesis::default();
        let mut store = ProofBuilder {
            store: &mut proofs,
            synthesis: &mut synthesis,
        };
        let term = store.store.term_dag.app("A".into(), vec![]);
        let premise = Proof {
            proposition: Proposition::new(term, term),
            justification: Justification::Fiat,
        };
        let left = store.store.id_to_proof.push(premise.clone());
        let right = store.store.id_to_proof.push(premise);
        let cases = [
            ("rule".to_owned(), 0, vec![left, right]),
            // Equal contents from distinct allocations must still share.
            (["ru", "le"].concat(), 0, vec![left, right]),
            ("rule".to_owned(), 1, vec![left, right]),
            ("rule".to_owned(), 0, vec![right, left]),
            ("other".to_owned(), 0, vec![left, right]),
            ("rule".to_owned(), 0, vec![left]),
            ("rule".to_owned(), 0, vec![left, left]),
            ("rule".to_owned(), 0, vec![]),
        ];
        let mut old_keys = IndexSet::default();
        for (name, column, premises) in &cases {
            let (old_index, _) = old_keys.insert_full((name.clone(), *column, premises.clone()));
            let firing = store.rule_firing(name, premises);
            let id = store.push_shared_proof(
                SynthKey::Rule(firing, *column),
                Proof {
                    proposition: Proposition::new(term, term),
                    justification: Justification::Rule {
                        name: name.clone(),
                        premise_proofs: premises.clone(),
                        substitution: IndexMap::default(),
                    },
                },
            );
            assert_eq!(id.index(), old_index + 2);
        }

        assert_eq!(store.store.id_to_proof.n_ids(), old_keys.len() + 2);
        let cloned = store.store.clone();
        assert_eq!(cloned.id_to_proof, store.store.id_to_proof);
        assert_eq!(cloned.term_dag, store.store.term_dag);
    }
}
