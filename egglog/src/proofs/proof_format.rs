use crate::{
    ResolvedCall, Term, TermDag, TermId,
    ast::{
        FunctionSubtype, GenericNCommand, ResolvedExpr, ResolvedFact, ResolvedNCommand,
        ResolvedRule,
    },
    proofs::{
        proof_checker::{
            ProofCheckError, ProofCheckErrorKind, eval_expr_with_subst, gather_globals, run_merge,
        },
        proof_encoding_helpers::{EncodingNames, Skeleton, recomputable_premises},
        proof_head::{Firing, HeadPlan, HeadWalk, ProofAlgebra},
    },
    typechecking::PrimitiveValidator,
    util::{HashMap, HashSet, IEntry, IndexMap, IndexSet, SymbolGen},
};
use egglog_ast::generic_ast::Literal;
use egglog_numeric_id::{DenseIdMap, NumericId, define_id};
use std::{fmt, rc::Rc};

define_id!(
    RawProofId,
    u32,
    "An identifier for a proof in a RawProofStore"
);
define_id!(pub ProofId, u32, "An identifier for a proof in a ProofStore");

impl fmt::Display for ProofId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.index())
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
/// merge-body subexpression yields its own conclusion. Used when converting a
/// `MergeFnIdx` raw proof into its `MergeFn` conclusion.
fn run_merge_subexpr(
    term_dag: &mut TermDag,
    func_name: &str,
    prog: &[ResolvedNCommand],
    old_term: TermId,
    new_term: TermId,
    idx: usize,
) -> Result<(TermId, HashSet<Proposition>), ProofCheckError> {
    let mut subst = HashMap::default();
    subst.insert("old".to_string(), old_term);
    subst.insert("new".to_string(), new_term);
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
            return eval_expr_with_subst("merge_function", subexpr, term_dag, &subst);
        }
    }
    Err(ProofCheckErrorKind::FunctionNotFound {
        function_name: func_name.to_string(),
    }
    .into())
}

/// A rule proof's columns, gathered across the chain of head proofs it is the
/// last of.
struct RuleColumns {
    name: String,
    /// One per premise the encoder recorded: the rule's written body facts, in
    /// order, then a lookup per global the head mentions.
    premises: Vec<TermId>,
    /// One per subterm the head interned before this row's proof, in construction
    /// order.
    bridges: Vec<TermId>,
    /// Which of the head's proofs the row asked about states, as an `i64` term
    /// (see [`crate::proofs::proof_head`]); the rows further down the chain state
    /// proofs from earlier in the head's walk.
    column: TermId,
}

/// A proof straight from the e-graph, not exposed to users.
struct RawProofStore {
    term_dag: TermDag,
    /// The proof constructor names, used to recognize each extracted proof
    /// term's head by exact match (rather than substring guessing).
    names: EncodingNames,
    /// The proofs parsed so far, hash-consed: a [`RawProofId`] is an index into
    /// it, and equal ids mean equal trees.
    store: IndexSet<RawProof>,
    term_to_proof: HashMap<TermId, RawProofId>,
}

pub(crate) fn proof_store_from_term(
    encoding_names: &EncodingNames,
    term_dag: TermDag,
    proof_term: TermId,
    prog: &Vec<ResolvedNCommand>,
    container_normalizers: HashMap<String, PrimitiveValidator>,
    prim_value_constructors: HashSet<String>,
) -> (ProofStore, ProofId) {
    let (raw_store, raw_proof_id) =
        RawProofStore::from_extracted(encoding_names, term_dag, proof_term);
    ProofStore::from_raw(
        prog,
        raw_store,
        raw_proof_id,
        container_normalizers,
        prim_value_constructors,
    )
}

/// Justifies a single grounded equality t1 = t2.
/// Corresponds closely to the proof header in [`proof_encoding_helpers.rs`](crate::proofs::proof_encoding_helpers).
/// Compared to [`Proof`], a [`RawProof`] leaves out the implicit [`Proposition`] being proven (in some cases) and
/// leaves off the implicit rule substitution.
/// Converting to a [`Proof`] with [`ProofStore::from_raw`] fills in these details.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
enum RawProof {
    /// Equalities added at the top level are justified by fiat.
    Fiat(TermId, TermId),
    /// Given a rule name and proofs for each premise, produces a proof of a
    /// grounded equality from the head of the rule. The substitution is implicit —
    /// in [`Justification::Rule`] it is explicit.
    ///
    /// The second list holds one *bridge* premise per subterm the head interned —
    /// the view-row proof that says which e-class it landed in — in construction
    /// order. The column names which proof of the head's lowering this is (see
    /// [`crate::proofs::proof_head`]); conversion derives the equality from that
    /// and the bridges, so the row stores no terms.
    Rule(String, Vec<RawProofId>, Vec<RawProofId>, i64),
    /// A term-free merge proof: given proofs `f(…, old) = f(…, old)` and
    /// `f(…, new) = f(…, new)`, the index `idx` identifies which subexpression of the
    /// merge body this justifies (a pre-order index over the body tree). The
    /// conclusion is reconstructed during conversion by evaluating subexpression
    /// `idx` on the premise outputs; the index distinguishes nested subexpressions
    /// that share the same premises. Used by the FD custom-function view merge, which
    /// runs without access to children.
    MergeFnIdx(String, RawProofId, RawProofId, usize),
    /// Like [`RawProof::MergeFnIdx`] but for the FD view row (no index). The conclusion
    /// `f(children) = eval(whole merge body)` is reconstructed during conversion by
    /// running the whole body on the two premise outputs. Used as the proof column of
    /// every FD pair-valued view's `:merge`.
    MergeFnRow(String, RawProofId, RawProofId),
    Trans(RawProofId, RawProofId),
    Sym(RawProofId),
    /// given a proof that t1 = f(..., ci, ...)
    /// and the child index i of ci in the term f(..., ci, ...)
    /// and a proof that ci = c2,
    /// produces a justification that t1 = f(..., c2, ...)
    Congr(RawProofId, usize, RawProofId),
    /// Given a proof that `t1 = c` and a child proof `a = b`, produces a
    /// justification that `t1 = c'` where every child of `c` equal to `a` is
    /// replaced by `b`. Minted by container rebuilds, which see elements in
    /// value order rather than the term form's canonical child order.
    /// Desugared by [`ProofStore::from_raw`] into positional
    /// [`Justification::Congr`] steps computed against the actual term.
    CongrAll(RawProofId, RawProofId),
    /// given a proof that t1 = f(..., ci, ...) and the child index i,
    /// produces a justification that ci = ci.
    Proj(RawProofId, usize),
    /// Given a proof that `t1 = c` and a term `a`, produces a justification that
    /// `a = a`, provided `a` is a child of `c`. Minted where the child's position
    /// in the term is not known at the site — a container's elements come in
    /// value order, and the term form orders them canonically. Desugared by
    /// [`ProofStore::from_raw`] into the positional [`RawProof::Proj`] computed
    /// against the actual term.
    ProjAll(RawProofId, TermId),
    /// Given a proof that `t1 = c` for a container term `c`, produces a proof of
    /// `t1 = normalize(c)` — the container's canonicalization (reorder/dedup/
    /// merge), which a structural `Congr` chain can't express.
    ContainerNormalize(RawProofId),
    /// Marks the proof of a container side condition (a container-producing
    /// primitive applied in a rule body). It carries nothing: the side condition
    /// is re-evaluated against the rule body when checked (see
    /// `check_side_condition`), so the proof needs no term.
    Eval,
}

/// A [`ProofStore`] is similar to a [`TermDag`].
/// It's a hash-consed arena enabling proofs to share sub-proofs.
/// We refer to proofs with a [`ProofId`] which is an index into the store, used with [`ProofStore::get`] to retrieve the proof.
#[derive(Clone)]
pub struct ProofStore {
    pub(super) term_dag: TermDag,
    proof_id: HashMap<RawProof, ProofId>,
    pub(super) id_to_proof: DenseIdMap<ProofId, Proof>,
    /// Container constructor head -> its validator (the container's term
    /// normalizer), used by [`ProofStore::normalize_container`].
    container_normalizers: HashMap<String, PrimitiveValidator>,
    /// Canonical value-term heads for base sorts whose values termify as
    /// applications (see `Sort::prim_value_constructor`). A term built from one of
    /// these heads over literals is a self-evident value, so the checker accepts a
    /// reflexive `Fiat` over it ([`ProofStore::reflexive_value_term`]).
    pub(super) prim_value_constructors: HashSet<String>,
    /// Rule name -> where the rule sits in the program being checked.
    rule_at: HashMap<String, usize>,
    /// Rule name -> how its head lowers.
    head_plans: HashMap<String, Rc<HeadPlan>>,
    /// (Rule name, body premises) -> how far that firing's head has been walked.
    /// Every rule proof of one firing reads a column out of the array that one
    /// walk fills.
    head_walks: HashMap<(String, Vec<ProofId>), HeadWalk>,
    /// Structural sharing for the proofs conversion synthesizes.
    synthesized: HashMap<SynthKey, ProofId>,
}

/// What a synthesized proof is, for sharing one node per distinct value.
#[derive(Clone, PartialEq, Eq, Hash)]
pub(crate) enum SynthKey {
    /// A rule head's own conclusion: the rule, which of its proofs, and the
    /// premises that fix the substitution.
    Rule(String, i64, Vec<ProofId>),
    Sym(ProofId),
    Trans(ProofId, ProofId),
    Congr(ProofId, usize, ProofId),
    /// A premise the encoding stored no row for (see [`recomputable_premises`]).
    Fiat(TermId, TermId),
}

impl fmt::Debug for ProofStore {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // `container_normalizers` holds closures (not `Debug`); show its heads.
        f.debug_struct("ProofStore")
            .field("term_dag", &self.term_dag)
            .field("proof_id", &self.proof_id)
            .field("id_to_proof", &self.id_to_proof)
            .field(
                "container_normalizers",
                &self.container_normalizers.keys().collect::<Vec<_>>(),
            )
            .finish()
    }
}

/// In egglog, all proofs prove a [`Proposition`], which is an equality between two terms.
/// An egglog e-graph is a partial equality relation, closed under symmetry, transitivity, and congruence.
///
/// Note that egglog does not assume reflexivity! For a term t, it's not assumed that t = t.
/// Once an egglog action adds a term, for example (Add 1 2), then the equality (Add 1 2) = (Add 1 2) can be proven.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct Proposition {
    pub lhs: TermId,
    pub rhs: TermId,
}

impl Proposition {
    /// Create a new proposition representing the equality lhs = rhs.
    pub fn new(lhs: TermId, rhs: TermId) -> Self {
        Proposition { lhs, rhs }
    }

    /// Get the left-hand side of the equality
    pub fn lhs(&self) -> TermId {
        self.lhs
    }

    /// Get the right-hand side of the equality
    pub fn rhs(&self) -> TermId {
        self.rhs
    }
}

/// A proof shows that a [`Proposition`] is true, justified by a [`Justification`].
#[derive(Clone, Debug)]
pub struct Proof {
    pub(super) proposition: Proposition,
    pub(super) justification: Justification,
}

/// Justifies a [`Proposition`] using one of several proof rules.
/// Some justifications are axioms of egglog, like Sym, Trans, and Congr.
/// Other justifications are based on user input, like Fiat, Rule, and MergeFn.
///
/// Compared to the crate-internal `RawProof`, a [`Justification`] is always paired with the
/// [`Proposition`] being proven (in a [`Proof`]).
/// Additionally, [`Justification::Rule`] includes the explicit substitution mapping variable names to terms,
/// while `RawProof::Rule` leaves this implicit.
#[derive(Clone, Debug)]
pub enum Justification {
    /// Equalities added at the top level are justified by fiat.
    /// Primitive reflexive equalities like 2 = 2 are also justified by Fiat.
    /// Reflexivity of equality is not assumed: a proof of `t = t`` must correspond to some `t` added at the top level.
    Fiat,
    /// Proves a grounded equality `t1 = t2` which appears
    /// in the body of a rule given a substitution given proofs
    /// for each premise ([`Fact`](crate::ast::Fact)) of the rule.
    /// If the [`Proposition`] proven is a term like `t = t`,
    /// t may be a subexpression of the body of the rule under the substitution.
    ///
    /// A proof for a premise is an equality t1 = t2 that matches the premise under some substitution.
    /// A proof for a premise that doesn't involve equality (i.e. (Add a b)) gives a proof of t1 = t2 where t2 matches the premise.
    /// A proof for a premise about a funciton (= (f a b ...) c) gives a proof (f a b ... c) = (f a b ... c).
    Rule {
        name: String,
        premise_proofs: Vec<ProofId>,
        /// Ordered by where each variable first occurs in the rule body.
        substitution: IndexMap<String, TermId>,
    },
    /// Given two proofs f(c1, c2, ..., old) = f(c1, c2, ..., old) and f(c1, c2, ..., new) = f(c1, c2, ..., new),
    /// proves either:
    /// 1. f(c1, c2, ..., merge_fn) = f(c1, c2, ..., merge_fn) where merge_fn is the merge function of function f applied to old and new, or
    /// 2. t = t where t is a subexpression of the merge function applied to old and new.
    MergeFn {
        function: String,
        old_proof: ProofId,
        new_proof: ProofId,
    },
    /// Given proofs of t1 = t2 and t2 = t3, produces a proof of t1 = t3.
    /// An axiom egglog assumes.
    Trans(ProofId, ProofId),
    /// Given a proof of t1 = t2, produces a proof of t2 = t1.
    /// An axiom egglog assumes.
    Sym(ProofId),
    /// Extends an equality proof with a congruence step.
    /// Given
    /// 1) a `proof` with proposition `t1 = f(..., ci, ...)`
    /// 2) and the `child_index` of `ci` in the term `f(..., ci, ...)`
    /// 3) and a child_proof with proposition ci = c2,
    ///
    /// proves `t1 = f(..., c2, ...)`.
    ///
    /// An axiom egglog assumes.
    Congr {
        proof: ProofId,
        child_index: usize,
        child_proof: ProofId,
    },
    /// Projects a subterm out of an equality already proven.
    /// Given
    /// 1) a `proof` with proposition `t1 = f(..., ci, ...)`
    /// 2) and the `child_index` of `ci` in the term `f(..., ci, ...)`,
    ///
    /// proves `ci = ci`.
    ///
    /// An axiom egglog assumes: a term only enters a provable equality once it
    /// has been built, and building it built its children.
    Proj { proof: ProofId, child_index: usize },
    /// Given a `proof` of `t1 = c` for a container term `c`, proves
    /// `t1 = normalize(c)` — the container's canonicalization (sort by
    /// [`TermDag::ast_cmp`]; dedup for sets; last-write-wins for maps). Sound by
    /// the assumption that normalization preserves the container's value; the
    /// checker recomputes it.
    ContainerNormalize { proof: ProofId },
    /// Marks the proof of a container side condition. It proves nothing on its
    /// own; the side condition is re-evaluated against the rule body when the
    /// rule is checked (see `check_side_condition`), which is what establishes
    /// the container's value. The `Proof`'s proposition is a placeholder.
    Eval,
}

/// The [`RawProof`] a constructor states, over its arguments and its
/// already-parsed nested proofs.
type BuildProof = fn(&RawProofStore, &[TermId], &[RawProofId]) -> RawProof;

/// How one proof constructor is read: how many arguments it takes, which of
/// them are nested proofs — in the order they are parsed — and what proof it
/// states over them. The rule and packed-row constructors are variadic and are
/// not described here; both readers special-case them.
struct ProofShape {
    arity: usize,
    children: &'static [usize],
    build: BuildProof,
}

impl RawProofStore {
    /// After extracting a proof from the e-graph, convert it to a [`RawProof`].
    pub(crate) fn from_extracted(
        encoding_names: &EncodingNames,
        term_dag: TermDag,
        term: TermId,
    ) -> (Self, RawProofId) {
        let mut store = RawProofStore {
            term_dag: term_dag.clone(),
            names: encoding_names.clone(),
            store: IndexSet::default(),
            term_to_proof: HashMap::default(),
        };
        store.parse_nested_first(term);
        let parsed = store.parse_proof(term);
        (store, parsed)
    }

    /// Parse the proofs nested in `term_id` deepest first, on an explicit stack,
    /// visiting them in the order [`Self::parse_proof`] would. It then finds each
    /// one already parsed, so a deep proof does not need a deep call stack.
    fn parse_nested_first(&mut self, term_id: TermId) {
        // `false` means the term's nested proofs still have to be pushed.
        let mut stack = vec![(term_id, false)];
        let mut seen: HashSet<TermId> = HashSet::default();
        while let Some((id, nested_pushed)) = stack.pop() {
            if nested_pushed {
                self.parse_proof(id);
                continue;
            }
            if !seen.insert(id) {
                continue;
            }
            stack.push((id, true));
            // Reversed, so popping visits them in `parse_proof_inner`'s order.
            stack.extend(
                self.nested_proofs(id)
                    .into_iter()
                    .rev()
                    .map(|nested| (nested, false)),
            );
        }
    }

    /// The proof terms [`Self::parse_proof_inner`] recurses into, in order. A
    /// malformed term reports none, leaving the diagnostic to the parse itself.
    fn nested_proofs(&self, term_id: TermId) -> Vec<TermId> {
        let Term::App(head, args) = self.term_dag.get(term_id) else {
            return vec![];
        };
        let names = &self.names;
        if names.fused_rule_arity(head).is_some() || *head == names.rule_link_constructor {
            let RuleColumns {
                premises, bridges, ..
            } = self.rule_columns(term_id);
            return premises.into_iter().chain(bridges).collect();
        }
        if let Some(columns) = names.packed_proof_columns(head)
            && args.len() == columns + 1
        {
            return args[1..].to_vec();
        }
        self.shape(head)
            .filter(|shape| shape.arity == args.len())
            .map_or(vec![], |shape| {
                shape.children.iter().map(|&at| args[at]).collect()
            })
    }

    /// How the proof constructor `head` names is read, or `None` when `head`
    /// names none.
    fn shape(&self, head: &str) -> Option<ProofShape> {
        let names = &self.names;
        let shape = |arity, children: &'static [usize], build: BuildProof| {
            Some(ProofShape {
                arity,
                children,
                build,
            })
        };
        if names.is_fiat(head) {
            shape(2, &[], |_, args, _| RawProof::Fiat(args[0], args[1]))
        } else if head == names.merge_fn_idx_constructor {
            shape(4, &[1, 2], |store, args, kids| {
                let function = store.parse_string(args[0]);
                RawProof::MergeFnIdx(function, kids[0], kids[1], store.parse_index(args[3]))
            })
        } else if head == names.merge_fn_row_constructor {
            shape(3, &[1, 2], |store, args, kids| {
                RawProof::MergeFnRow(store.parse_string(args[0]), kids[0], kids[1])
            })
        } else if head == names.eq_trans_constructor {
            shape(2, &[0, 1], |_, _, kids| RawProof::Trans(kids[0], kids[1]))
        } else if head == names.eq_sym_constructor {
            shape(1, &[0], |_, _, kids| RawProof::Sym(kids[0]))
        } else if head == names.container_normalize_constructor {
            shape(1, &[0], |_, _, kids| RawProof::ContainerNormalize(kids[0]))
        } else if head == names.congr_constructor {
            shape(3, &[0, 2], |store, args, kids| {
                RawProof::Congr(kids[0], store.parse_index(args[1]), kids[1])
            })
        } else if head == names.congr_all_constructor {
            shape(2, &[0, 1], |_, _, kids| {
                RawProof::CongrAll(kids[0], kids[1])
            })
        } else if head == names.proj_constructor {
            shape(2, &[0], |store, args, kids| {
                RawProof::Proj(kids[0], store.parse_index(args[1]))
            })
        } else if names.is_proj_all(head) {
            shape(2, &[0], |_, args, kids| RawProof::ProjAll(kids[0], args[1]))
        } else if head == names.eval_constructor {
            shape(0, &[], |_, _, _| RawProof::Eval)
        } else {
            None
        }
    }

    /// Read a rule proof's columns, walking the chain of links a head adds one of
    /// per proof it composes.
    ///
    /// The premises and the bridges are told apart structurally rather than by
    /// counting: the row ending the chain carries every premise inline, and each
    /// link adds exactly one bridge. The column returned is the outermost row's,
    /// read at the index that row's own asserted arity fixes.
    fn rule_columns(&self, term_id: TermId) -> RuleColumns {
        let mut bridges = vec![];
        let mut column = None;
        let mut cell = term_id;
        loop {
            let Term::App(head, args) = self.term_dag.get(cell) else {
                panic!("expected a rule proof term. Proof parsing assumes valid proofs.");
            };
            if *head == self.names.rule_link_constructor {
                assert!(args.len() == 3, "{head} should have 3 args");
                column.get_or_insert(args[2]);
                bridges.push(args[1]);
                cell = args[0];
                continue;
            }
            let Some(arity) = self.names.fused_rule_arity(head) else {
                panic!(
                    "expected a rule proof constructor, got {head}. Proof parsing assumes valid proofs."
                );
            };
            assert!(
                args.len() == arity + 2,
                "{head} should have {} args",
                arity + 2
            );
            // Recorded newest first, since a subterm's view-row proof is only
            // readable once the subterm is interned.
            bridges.reverse();
            return RuleColumns {
                name: self.parse_string(args[0]),
                premises: args[1..arity + 1].to_vec(),
                bridges,
                column: *column.get_or_insert(args[arity + 1]),
            };
        }
    }

    fn parse_proof(&mut self, term_id: TermId) -> RawProofId {
        if let Some(&proof_id) = self.term_to_proof.get(&term_id) {
            return proof_id;
        }

        let proof_id = self.parse_proof_inner(term_id);
        self.term_to_proof.insert(term_id, proof_id);
        proof_id
    }

    /// [`Self::parse_proof`] for one of the term's own nested proofs, which
    /// [`Self::parse_nested_first`] has already parsed. A child that pre-pass
    /// misses recurses from here instead, at the call depth it exists to avoid.
    fn child_proof(&mut self, term_id: TermId) -> RawProofId {
        debug_assert!(
            self.term_to_proof.contains_key(&term_id),
            "proof child {term_id:?} was not visited before its parent"
        );
        self.parse_proof(term_id)
    }

    /// The composition `skeleton` states, over the proof columns `columns` of a
    /// packed row.
    fn instantiate(&mut self, skeleton: &Skeleton, columns: &[TermId]) -> RawProofId {
        let proof = match skeleton {
            Skeleton::Leaf(column) => return self.child_proof(columns[*column]),
            Skeleton::Sym(inner) => RawProof::Sym(self.instantiate(inner, columns)),
            Skeleton::Trans(left, right) => {
                let left = self.instantiate(left, columns);
                RawProof::Trans(left, self.instantiate(right, columns))
            }
            Skeleton::Congr(base, child, step) => {
                let base = self.instantiate(base, columns);
                RawProof::Congr(base, *child, self.instantiate(step, columns))
            }
            Skeleton::Proj(base, child) => RawProof::Proj(self.instantiate(base, columns), *child),
        };
        self.add_proof(proof)
    }

    fn parse_proof_inner(&mut self, term_id: TermId) -> RawProofId {
        let term = self.term_dag.get(term_id).clone();
        let Term::App(head, args) = term else {
            panic!(
                "Expected proof term to be an app, got {term:?}. Proof parsing assumes valid proofs."
            );
        };

        if let Some(columns) = self.names.packed_proof_columns(&head) {
            assert!(
                args.len() == columns + 1,
                "{head} should have {} args",
                columns + 1
            );
            let spelling = self.parse_string(args[0]);
            let skeleton = Skeleton::from_spelling(&spelling)
                .filter(|skeleton| skeleton.width() <= columns)
                .unwrap_or_else(|| {
                    panic!("{spelling} is not a composition over {head}'s {columns} columns")
                });
            return self.instantiate(&skeleton, &args[1..]);
        }

        if self.names.fused_rule_arity(&head).is_some() || head == self.names.rule_link_constructor
        {
            let RuleColumns {
                name,
                premises,
                bridges,
                column,
            } = self.rule_columns(term_id);
            let premises = premises.iter().map(|arg| self.child_proof(*arg)).collect();
            let bridges = bridges.iter().map(|arg| self.child_proof(*arg)).collect();
            let column = self.parse_int(column);
            return self.add_proof(RawProof::Rule(name, premises, bridges, column));
        }

        let shape = self.shape(&head).unwrap_or_else(|| {
            panic!("Unrecognized proof term head: {head}. Proof parsing assumes valid proofs.")
        });
        assert!(
            args.len() == shape.arity,
            "{head} should have {} args",
            shape.arity
        );
        let children: Vec<RawProofId> = shape
            .children
            .iter()
            .map(|&at| self.child_proof(args[at]))
            .collect();
        let proof = (shape.build)(self, &args, &children);

        self.add_proof(proof)
    }

    fn parse_string(&self, term_id: TermId) -> String {
        match self.term_dag.get(term_id) {
            Term::Lit(Literal::String(s)) => s.clone(),
            other => panic!(
                "expected string literal in proof term, got {other:?}. Proof parsing expects valid proofs."
            ),
        }
    }

    fn parse_index(&self, term_id: TermId) -> usize {
        match self.term_dag.get(term_id) {
            Term::Lit(Literal::Int(i)) if *i >= 0 => *i as usize,
            other => {
                panic!("expected non-negative integer literal for congruence index, got {other:?}")
            }
        }
    }

    fn parse_int(&self, term_id: TermId) -> i64 {
        match self.term_dag.get(term_id) {
            Term::Lit(Literal::Int(i)) => *i,
            other => panic!("expected integer literal in proof term, got {other:?}"),
        }
    }

    fn add_proof(&mut self, proof: RawProof) -> RawProofId {
        if let Some(id) = self.store.get_index_of(&proof) {
            return RawProofId::from_usize(id);
        }
        self.store.insert(proof);
        RawProofId::from_usize(self.store.len() - 1)
    }
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

impl ProofStore {
    /// Get the term DAG used by this proof store.
    pub fn term_dag(&self) -> &TermDag {
        &self.term_dag
    }

    /// Recompute a container term's canonical form by applying the constructor
    /// validator registered for its head (the container's own term normalizer).
    /// Non-container terms, and heads with no validator, are returned unchanged.
    pub(super) fn normalize_container(&mut self, term_id: TermId) -> TermId {
        let Term::App(head, args) = self.term_dag.get(term_id).clone() else {
            return term_id;
        };
        let Some(validator) = self.container_normalizers.get(&head).cloned() else {
            return term_id;
        };
        validator(&mut self.term_dag, &args).unwrap_or(term_id)
    }

    /// Get the [`Proof`] with the given id.
    /// Panics if the id is invalid (if it came from another proof store, for example).
    pub fn get(&self, proof_id: ProofId) -> &Proof {
        &self.id_to_proof[proof_id]
    }

    /// Add a proof, sharing one node per distinct `key`. The e-graph
    /// hash-conses its own proof rows, so the proofs conversion rebuilds in their
    /// place must be shared too — otherwise a subproof reached along several paths
    /// becomes a fresh copy per path, and the proof unfolds into a tree.
    pub(super) fn push_shared_proof(&mut self, key: SynthKey, proof: Proof) -> ProofId {
        if let Some(&id) = self.synthesized.get(&key) {
            return id;
        }
        let id = self.id_to_proof.push(proof);
        self.synthesized.insert(key, id);
        id
    }

    /// Get a string representation of the proof with the given id.
    /// The string representation is a pretty-printed s-expression block with
    /// let bindings for sub-proofs and sub-terms.
    pub fn proof_to_string(&self, proof_id: ProofId) -> String {
        let symbol_gen = &mut crate::util::SymbolGen::new("".to_string());
        let mut buffer = String::new();
        symbol_gen.include_zero(true);
        let res = self.print_to_buffer(symbol_gen, proof_id, &mut buffer);
        buffer.push_str(&res);
        buffer
    }

    /// An empty store over `term_dag`.
    pub(super) fn new(
        term_dag: TermDag,
        container_normalizers: HashMap<String, PrimitiveValidator>,
        prim_value_constructors: HashSet<String>,
    ) -> ProofStore {
        ProofStore {
            term_dag,
            proof_id: HashMap::default(),
            id_to_proof: DenseIdMap::new(),
            container_normalizers,
            prim_value_constructors,
            rule_at: HashMap::default(),
            head_plans: HashMap::default(),
            head_walks: HashMap::default(),
            synthesized: HashMap::default(),
        }
    }

    fn from_raw(
        prog: &Vec<ResolvedNCommand>,
        raw_store: RawProofStore,
        raw_proof_id: RawProofId,
        container_normalizers: HashMap<String, PrimitiveValidator>,
        prim_value_constructors: HashSet<String>,
    ) -> (ProofStore, ProofId) {
        let mut store = ProofStore::new(
            raw_store.term_dag.clone(),
            container_normalizers,
            prim_value_constructors,
        );
        for (at, command) in prog.iter().enumerate() {
            if let ResolvedNCommand::NormRule { rule } = command {
                store.rule_at.entry(rule.name.clone()).or_insert(at);
            }
        }
        let globals = gather_globals(prog, &mut store.term_dag)
            .unwrap_or_else(|_| panic!("failed to gather globals from program"));

        let proof_id = store.convert_raw_proof(prog, &globals, &raw_store, raw_proof_id);
        (store, proof_id)
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
    fn reflexivize_premise(&mut self, premise_id: ProofId) -> ProofId {
        let prop = &self.id_to_proof[premise_id].proposition;
        if prop.lhs == prop.rhs {
            return premise_id;
        }
        // Shared, so the two rows of one firing reflexivize a premise to the
        // same id: the premise vector is both the walk memo's key and the
        // rule proofs' sharing key.
        self.reflexive(premise_id)
    }

    /// The two `MergeFn*` premise proofs end (rhs) at the colliding view terms
    /// `f(inputs.., output)`. Extract the view head, the shared input args,
    /// and the two output values from the premises' rhs (read before reflexivizing).
    fn merge_premise_view(
        &self,
        old_proof_id: ProofId,
        new_proof_id: ProofId,
    ) -> (String, Vec<TermId>, TermId, TermId) {
        let old_view = self.id_to_proof[old_proof_id].rhs();
        let new_view = self.id_to_proof[new_proof_id].rhs();
        match (self.term_dag.get(old_view), self.term_dag.get(new_view)) {
            (Term::App(old_head, old_args), Term::App(_new_head, new_args)) => {
                let head = old_head.clone();
                let old_output = *old_args.last().expect("merge view term has no args");
                let new_output = *new_args.last().expect("merge view term has no args");
                let inputs = old_args[..old_args.len() - 1].to_vec();
                (head, inputs, old_output, new_output)
            }
            _ => panic!(
                "MergeFn premise proofs should prove function application terms, got {:?} and {:?}",
                self.term_dag.get(old_view),
                self.term_dag.get(new_view)
            ),
        }
    }

    /// Build a `MergeFn` proof of `to_prove = to_prove` from the two premises,
    /// reflexivizing each ([`ProofStore::reflexivize_premise`]).
    fn merge_fn_proof(
        &mut self,
        function: &str,
        old_proof_id: ProofId,
        new_proof_id: ProofId,
        to_prove: TermId,
    ) -> Proof {
        let old_proof = self.reflexivize_premise(old_proof_id);
        let new_proof = self.reflexivize_premise(new_proof_id);
        Proof {
            proposition: Proposition::new(to_prove, to_prove),
            justification: Justification::MergeFn {
                function: function.to_string(),
                old_proof,
                new_proof,
            },
        }
    }

    /// Converts a raw proof into a user-facing proof, recursively converting sub-proofs as needed.
    /// This adds new metadata to the proof, such as the substitution for rules.
    ///
    /// Panics if the raw proof is invalid with respect to the program.
    fn convert_raw_proof(
        &mut self,
        prog: &Vec<ResolvedNCommand>,
        globals: &HashMap<String, TermId>,
        raw_store: &RawProofStore,
        raw_proof_id: RawProofId,
    ) -> ProofId {
        if let Some(&id) = self.proof_id.get(&raw_store.store[raw_proof_id.index()]) {
            return id;
        }
        let raw_proof = &raw_store.store[raw_proof_id.index()];

        let proof = match raw_proof {
            RawProof::Fiat(lhs, rhs) => Proof {
                proposition: Proposition::new(*lhs, *rhs),
                justification: Justification::Fiat,
            },
            RawProof::Rule(name, premise_proofs, bridge_proofs, raw_column) => {
                let rule = self.rule_named(prog, name);
                let planned = self.head_plan(rule);
                let (converted_premises, substitution) =
                    self.rule_premises(prog, globals, raw_store, name, rule, premise_proofs);

                // This row carries on the walk the last row of the same firing
                // left off at. A row reached while this one walks starts its own,
                // so the further of the two is the one kept.
                let firing_key = (name.clone(), converted_premises.clone());
                let carried = self.head_walks.remove(&firing_key);
                // A carried walk brings the bindings the earlier row seeded it
                // with, so only a walk starting from scratch needs them.
                let bindings = match &carried {
                    Some(_) => HashMap::default(),
                    None => {
                        let mut bindings = globals.clone();
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
                    converted_premises,
                    recorded,
                    Box::new(move |store: &mut ProofStore, _to_canonical| {
                        let raw = *bridge_proofs.get(next)?;
                        next += 1;
                        Some(store.convert_raw_proof(prog, globals, raw_store, raw))
                    }),
                );
                if let Some(walk) = carried {
                    firing.carry_on(walk);
                }
                let proof_id = firing.column(self, *raw_column);
                let walked = firing.into_walk();
                let further = self
                    .head_walks
                    .get(&firing_key)
                    .is_none_or(|kept| kept.reaches() < walked.reaches());
                if further {
                    self.head_walks.insert(firing_key, walked);
                }
                self.proof_id.insert(raw_proof.clone(), proof_id);
                return proof_id;
            }
            RawProof::MergeFnIdx(function, old_raw, new_raw, idx) => {
                let old_proof_id = self.convert_raw_proof(prog, globals, raw_store, *old_raw);
                let new_proof_id = self.convert_raw_proof(prog, globals, raw_store, *new_raw);
                // `idx` indexes all body nodes (pre-order, top node included). The
                // conclusion is that node's own minted term, i.e. its existence proof in
                // its FD view. The whole-view-row conclusion comes from `MergeFnRow`.
                let (_head, _inputs, old_output, new_output) =
                    self.merge_premise_view(old_proof_id, new_proof_id);
                let (to_prove, _props) = run_merge_subexpr(
                    &mut self.term_dag,
                    function,
                    prog,
                    old_output,
                    new_output,
                    *idx,
                )
                .unwrap_or_else(|e| {
                    panic!("failed to run merge subexpr {idx} for {function}: {e}")
                });
                self.merge_fn_proof(function, old_proof_id, new_proof_id, to_prove)
            }
            RawProof::MergeFnRow(function, old_raw, new_raw) => {
                let old_proof_id = self.convert_raw_proof(prog, globals, raw_store, *old_raw);
                let new_proof_id = self.convert_raw_proof(prog, globals, raw_store, *new_raw);
                // The conclusion is the whole view row `f(inputs..., merged)`, where
                // `merged` is the whole merge body evaluated on the two premise outputs.
                let (view_head, input_args, old_output, new_output) =
                    self.merge_premise_view(old_proof_id, new_proof_id);
                let (merged_child, _props) =
                    run_merge(&mut self.term_dag, function, prog, old_output, new_output)
                        .unwrap_or_else(|e| panic!("failed to run merge for {function}: {e}"));
                let mut merged_args = input_args;
                merged_args.push(merged_child);
                let to_prove = self.term_dag.app(view_head, merged_args);
                self.merge_fn_proof(function, old_proof_id, new_proof_id, to_prove)
            }
            RawProof::Trans(left_raw, right_raw) => {
                let left_id = self.convert_raw_proof(prog, globals, raw_store, *left_raw);
                let right_id = self.convert_raw_proof(prog, globals, raw_store, *right_raw);
                let left = &self.id_to_proof[left_id];
                let right = &self.id_to_proof[right_id];
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
                let inner_id = self.convert_raw_proof(prog, globals, raw_store, *inner_raw);
                let inner = &self.id_to_proof[inner_id];
                Proof {
                    proposition: Proposition::new(inner.rhs(), inner.lhs()),
                    justification: Justification::Sym(inner_id),
                }
            }
            RawProof::Congr(proof_raw, child_index, child_raw) => {
                let base_id = self.convert_raw_proof(prog, globals, raw_store, *proof_raw);
                let child_id = self.convert_raw_proof(prog, globals, raw_store, *child_raw);
                let base_lhs = self.id_to_proof[base_id].lhs();
                let base_rhs = self.id_to_proof[base_id].rhs();
                let child_rhs = self.id_to_proof[child_id].rhs();
                self.assert_congr_starts_at_child(base_rhs, *child_index, child_id);
                let rhs = self.replace_term_child(base_rhs, *child_index, child_rhs);

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
                let inner_id = self.convert_raw_proof(prog, globals, raw_store, *inner_raw);
                let child = self.term_child(self.id_to_proof[inner_id].rhs(), *child_index);
                Proof {
                    proposition: Proposition::new(child, child),
                    justification: Justification::Proj {
                        proof: inner_id,
                        child_index: *child_index,
                    },
                }
            }
            RawProof::ProjAll(inner_raw, child_term) => {
                let inner_id = self.convert_raw_proof(prog, globals, raw_store, *inner_raw);
                let rhs = self.id_to_proof[inner_id].rhs();
                let Term::App(head, children) = self.term_dag.get(rhs) else {
                    panic!("element projection requires an application term, got {rhs:?}");
                };
                let child_index = children
                    .iter()
                    .position(|child| child == child_term)
                    .unwrap_or_else(|| {
                        panic!(
                            "element projection: {} is no child of {head}",
                            self.term_dag.to_string(*child_term)
                        )
                    });
                let positional = RawProof::Proj(*inner_raw, child_index);
                let projected = match self.proof_id.get(&positional) {
                    Some(&id) => id,
                    None => {
                        let id = self.id_to_proof.push(Proof {
                            proposition: Proposition::new(*child_term, *child_term),
                            justification: Justification::Proj {
                                proof: inner_id,
                                child_index,
                            },
                        });
                        self.proof_id.insert(positional, id);
                        id
                    }
                };
                self.proof_id.insert(raw_proof.clone(), projected);
                return projected;
            }
            RawProof::CongrAll(proof_raw, child_raw) => {
                let base_id = self.convert_raw_proof(prog, globals, raw_store, *proof_raw);
                let child_id = self.convert_raw_proof(prog, globals, raw_store, *child_raw);
                let expanded_id = self.expand_congr_all(base_id, child_id);
                self.proof_id.insert(raw_proof.clone(), expanded_id);
                return expanded_id;
            }
            RawProof::ContainerNormalize(inner_raw) => {
                let inner_id = self.convert_raw_proof(prog, globals, raw_store, *inner_raw);
                let inner_lhs = self.id_to_proof[inner_id].lhs();
                let inner_rhs = self.id_to_proof[inner_id].rhs();
                let normalized = self.normalize_container(inner_rhs);
                Proof {
                    proposition: Proposition::new(inner_lhs, normalized),
                    justification: Justification::ContainerNormalize { proof: inner_id },
                }
            }
            RawProof::Eval => {
                // The marker proves nothing on its own; `check_side_condition`
                // re-evaluates the side condition against the rule body. Give it
                // a placeholder proposition (the `Proof` struct requires one).
                let placeholder = self.term_dag.app("@side-condition".to_string(), vec![]);
                Proof {
                    proposition: Proposition::new(placeholder, placeholder),
                    justification: Justification::Eval,
                }
            }
        };

        let proof_id = self.id_to_proof.push(proof);
        self.proof_id.insert(raw_proof.clone(), proof_id);
        proof_id
    }

    /// The rule the proof names, which the encoder guarantees is in the program.
    fn rule_named<'a>(&self, prog: &'a [ResolvedNCommand], rule_name: &str) -> &'a ResolvedRule {
        let at = *self
            .rule_at
            .get(rule_name)
            .unwrap_or_else(|| panic!("could not find rule with name {rule_name}"));
        match &prog[at] {
            ResolvedNCommand::NormRule { rule } => rule,
            _ => unreachable!("only a rule is recorded"),
        }
    }

    /// How `rule`'s head lowers. A property of the rule text, so it is computed
    /// once per rule.
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
        prog: &Vec<ResolvedNCommand>,
        globals: &HashMap<String, TermId>,
        raw_store: &RawProofStore,
        name: &str,
        rule: &ResolvedRule,
        premise_proofs: &[RawProofId],
    ) -> (Vec<ProofId>, IndexMap<String, TermId>) {
        let recomputable = recomputable_premises(&rule.body, &|var| globals.contains_key(var));
        let mut stored = premise_proofs.iter();
        let mut substitution = IndexMap::default();
        let mut converted = Vec::with_capacity(rule.body.len());
        for (fact, recomputable) in rule.body.iter().zip(recomputable) {
            let premise = if recomputable {
                self.recomputed_premise(name, fact, &substitution)
            } else {
                let raw = *stored.next().unwrap_or_else(|| {
                    panic!(
                        "rule {name} recorded {} premises for a body of {} facts",
                        premise_proofs.len(),
                        rule.body.len()
                    )
                });
                let premise = self.convert_raw_proof(prog, globals, raw_store, raw);
                // Rebuild/canonicalization can rewrite a matched custom-function-fact
                // premise `(= (f args) v)` into a non-reflexive natural->canonical
                // `Congr` proof `(f nat) = (f canon)` (e.g. when an argument's e-class
                // has several equivalent shapes from commutativity/associativity
                // rewrites). The checker's function-fact normal form expects a
                // reflexive premise at the matched (canonical) shape, so reflexivize
                // those. Equality-fact premises `(= a b)` must stay non-reflexive.
                if is_custom_func_fact(fact) {
                    self.reflexivize_premise(premise)
                } else {
                    premise
                }
            };
            // Container side conditions carry only an `Eval` marker (no value);
            // their bindings are generated by `check_side_condition` at check
            // time, so there is nothing to unify here.
            if !crate::proofs::proof_checker::is_container_side_condition(fact) {
                self.unify_fact(fact, premise, &mut substitution);
            }
            converted.push(premise);
        }
        (converted, substitution)
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
            eval_expr_with_subst(rule_name, expr, &mut store.term_dag, &bindings)
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
                ResolvedExpr::Call(_span2, head @ ResolvedCall::Func(func_type), args),
                ResolvedExpr::Var(_span3, v),
            ) if func_type.subtype == FunctionSubtype::Custom => {
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
                        "expected function application term for call {}, got {:?}. Conversion from raw proofs assumes valid proofs with respect to the program.",
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
        loop {
            let lhs = self.id_to_proof[current].lhs();
            let rhs = self.id_to_proof[current].rhs();
            let Term::App(_, children) = self.term_dag.get(rhs) else {
                panic!("congr-all requires an application term. Conversion assumes valid proofs.");
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
            "congruence step {child_index} does not start at that child"
        );
    }

    /// The child of an application term at `child_index`. Panics when the term
    /// is not an application, or has no such child.
    pub(super) fn term_child(&self, term_id: TermId, child_index: usize) -> TermId {
        let Term::App(head, args) = self.term_dag.get(term_id) else {
            panic!("projection requires an application term");
        };
        *args.get(child_index).unwrap_or_else(|| {
            panic!(
                "projection index {child_index} out of bounds for {head} with {} children",
                args.len()
            )
        })
    }

    pub(super) fn replace_term_child(
        &mut self,
        term_id: TermId,
        child_index: usize,
        new_child: TermId,
    ) -> TermId {
        let term = self.term_dag.get(term_id).clone();
        let Term::App(head, args) = term else {
            panic!("congruence requires an application term");
        };
        assert!(
            child_index < args.len(),
            "congruence child index {child_index} out of bounds for term with {} children",
            args.len()
        );

        let updated_children: Vec<TermId> = args
            .iter()
            .enumerate()
            .map(|(idx, child_id)| {
                if idx == child_index {
                    new_child
                } else {
                    *child_id
                }
            })
            .collect();

        self.term_dag.app(head.clone(), updated_children)
    }

    /// Print a proof with the given id, with subproofs and terms
    /// added as let bindings in `buffer`.
    /// Returns the printed proof string.
    fn print_to_buffer(
        &self,
        symbol_gen: &mut SymbolGen,
        proof_id: ProofId,
        buffer: &mut String,
    ) -> String {
        let mut dag = self.term_dag.clone();
        let mut cache = HashMap::default();
        let proof_term_id = self.proof_to_term_for_printing(&mut dag, proof_id, &mut cache);
        dag.to_string_with_let_internal(symbol_gen, proof_term_id, buffer, |constructor| {
            match constructor {
                "=" => "prop".to_string(),
                "Fiat" | "Rule" | "Merge" | "Trans" | "Sym" | "Congr" | "Proj"
                | "ContainerNormalize" | "Eval" => "prf".to_string(),
                _ => "t".to_string(),
            }
        })
    }

    fn proof_to_term_for_printing(
        &self,
        dag: &mut TermDag,
        proof_id: ProofId,
        cache: &mut HashMap<ProofId, TermId>,
    ) -> TermId {
        if let Some(&term_id) = cache.get(&proof_id) {
            return term_id;
        }

        let proof = &self.id_to_proof[proof_id];

        // Helper to create (= lhs rhs) term
        let make_equality = |dag: &mut TermDag, lhs: TermId, rhs: TermId| -> TermId {
            dag.app("=".to_string(), vec![lhs, rhs])
        };

        let term_id = match &proof.justification {
            Justification::Fiat => {
                let equality = make_equality(dag, proof.lhs(), proof.rhs());
                dag.app("Fiat".to_string(), vec![equality])
            }
            Justification::Rule {
                name,
                premise_proofs,
                substitution,
            } => {
                let equality = make_equality(dag, proof.lhs(), proof.rhs());
                let name_literal = dag.lit(Literal::String(name.clone()));
                let name_term = dag.app("name".to_string(), vec![name_literal]);

                let premise_terms: Vec<TermId> = premise_proofs
                    .iter()
                    .map(|pid| self.proof_to_term_for_printing(dag, *pid, cache))
                    .collect();
                let premises_term = dag.app("premises".to_string(), premise_terms);

                let substitution_terms: Vec<TermId> = substitution
                    .iter()
                    .map(|(var, term_id)| dag.app(var.clone(), vec![*term_id]))
                    .collect();
                let substitution_term = dag.app("substitution".to_string(), substitution_terms);

                dag.app(
                    "Rule".to_string(),
                    vec![equality, name_term, premises_term, substitution_term],
                )
            }
            Justification::MergeFn {
                function,
                old_proof,
                new_proof,
            } => {
                let equality = make_equality(dag, proof.lhs(), proof.rhs());
                let old_term_id = self.proof_to_term_for_printing(dag, *old_proof, cache);
                let new_term_id = self.proof_to_term_for_printing(dag, *new_proof, cache);
                let function_term = dag.var(function.clone());
                dag.app(
                    "Merge".to_string(),
                    vec![equality, function_term, old_term_id, new_term_id],
                )
            }
            Justification::Trans(left, right) => {
                let equality = make_equality(dag, proof.lhs(), proof.rhs());
                let left_term_id = self.proof_to_term_for_printing(dag, *left, cache);
                let right_term_id = self.proof_to_term_for_printing(dag, *right, cache);
                dag.app(
                    "Trans".to_string(),
                    vec![equality, left_term_id, right_term_id],
                )
            }
            Justification::Sym(inner) => {
                let equality = make_equality(dag, proof.lhs(), proof.rhs());
                let inner_term_id = self.proof_to_term_for_printing(dag, *inner, cache);
                dag.app("Sym".to_string(), vec![equality, inner_term_id])
            }
            Justification::Congr {
                proof: base,
                child_index,
                child_proof,
            } => {
                let equality = make_equality(dag, proof.lhs(), proof.rhs());
                let base_term_id = self.proof_to_term_for_printing(dag, *base, cache);
                let child_term_id = self.proof_to_term_for_printing(dag, *child_proof, cache);
                let index_term = dag.lit(Literal::Int(*child_index as i64));
                dag.app(
                    "Congr".to_string(),
                    vec![equality, base_term_id, child_term_id, index_term],
                )
            }
            Justification::Proj {
                proof: base,
                child_index,
            } => {
                let equality = make_equality(dag, proof.lhs(), proof.rhs());
                let base_term_id = self.proof_to_term_for_printing(dag, *base, cache);
                let index_term = dag.lit(Literal::Int(*child_index as i64));
                dag.app("Proj".to_string(), vec![equality, base_term_id, index_term])
            }
            Justification::ContainerNormalize { proof: inner } => {
                let equality = make_equality(dag, proof.lhs(), proof.rhs());
                let inner_term_id = self.proof_to_term_for_printing(dag, *inner, cache);
                dag.app(
                    "ContainerNormalize".to_string(),
                    vec![equality, inner_term_id],
                )
            }
            Justification::Eval => dag.app("Eval".to_string(), vec![]),
        };

        cache.insert(proof_id, term_id);
        term_id
    }
}

impl Proof {
    /// Get the proposition the proof proves
    pub fn proposition(&self) -> &Proposition {
        &self.proposition
    }

    /// Get the left-hand side of the proven equality
    pub fn lhs(&self) -> TermId {
        self.proposition.lhs()
    }
    /// Get the right-hand side of the proven equality
    pub fn rhs(&self) -> TermId {
        self.proposition.rhs()
    }

    /// Get the justification for the proof
    pub fn justification(&self) -> &Justification {
        &self.justification
    }
}

/// A packed row unpacks to exactly the composition its skeleton states. The
/// compositions below are written out by hand rather than generated, so they are
/// an oracle rather than a second copy of the instantiation.
///
/// [`RawProofStore::add_proof`] hash-conses, so the unpacked row and the
/// hand-written chain land on the same [`RawProofId`] exactly when they are the
/// same tree, which is where `assert_agree` compares them.
#[cfg(test)]
mod tests {
    use super::*;
    use crate::proofs::proof_encoding_rebuild::rebuild_skeleton;
    use crate::util::SymbolGen;

    /// One firing of a rebuild rule over a four-child view row, as the proofs
    /// the rule packs: the row proof `e_old = f(old0 old1 old2 old3)`, a step
    /// per child column (column 3's is reflexive — that column did not move),
    /// and the e-class's own move `e_old = e_new`.
    struct RebuildFiring {
        raw: RawProofStore,
        row: TermId,
        /// `old_j = new_j`, per column.
        steps: Vec<TermId>,
        /// `e_old = e_new`.
        eclass: TermId,
        old: Vec<TermId>,
        /// Each column's canonical form; column 3's is its old one.
        new: Vec<TermId>,
        e_old: TermId,
        e_new: TermId,
    }

    impl RebuildFiring {
        fn new() -> RebuildFiring {
            let mut raw = empty_store();
            let leaf = |raw: &mut RawProofStore, name: String| raw.term_dag.app(name, vec![]);
            let old: Vec<TermId> = (0..4).map(|j| leaf(&mut raw, format!("old{j}"))).collect();
            let new: Vec<TermId> = (0..4)
                .map(|j| match j {
                    3 => old[3],
                    _ => leaf(&mut raw, format!("new{j}")),
                })
                .collect();
            let e_old = leaf(&mut raw, "e_old".to_string());
            let e_new = leaf(&mut raw, "e_new".to_string());

            let row_term = raw.term_dag.app("f".to_string(), old.clone());
            let row = fiat_term(&mut raw, e_old, row_term);
            let steps = (0..4)
                .map(|j| fiat_term(&mut raw, old[j], new[j]))
                .collect();
            let eclass = fiat_term(&mut raw, e_old, e_new);
            RebuildFiring {
                raw,
                row,
                steps,
                eclass,
                old,
                new,
                e_old,
                e_new,
            }
        }

        /// The proposition `lhs = f(children)`.
        fn concludes(&mut self, lhs: TermId, children: Vec<TermId>) -> Proposition {
            let rhs = self.raw.term_dag.app("f".to_string(), children);
            Proposition::new(lhs, rhs)
        }

        /// The proof of one of this firing's columns.
        fn proof(&mut self, column: TermId) -> RawProofId {
            self.raw.parse_proof(column)
        }

        /// [`assert_agree`] over this firing's store.
        fn assert_agree(&self, packed: RawProofId, chain: RawProofId, expected: &Proposition) {
            assert_agree(&self.raw, packed, chain, expected);
        }
    }

    /// Require that the unpacked row `packed` is the same tree as the chain it
    /// packs, and that the chain proves `expected`.
    fn assert_agree(
        raw: &RawProofStore,
        packed: RawProofId,
        chain: RawProofId,
        expected: &Proposition,
    ) {
        let mut store =
            ProofStore::new(raw.term_dag.clone(), HashMap::default(), HashSet::default());
        let prog = vec![];
        let globals = HashMap::default();
        let mut convert = |id| {
            let converted = store.convert_raw_proof(&prog, &globals, raw, id);
            store.simplify(converted)
        };
        let (packed_proof, chain_proof) = (convert(packed), convert(chain));
        assert_eq!(store.get(chain_proof).proposition(), expected);
        assert_eq!(
            packed,
            chain,
            "the unpacked row\n{}\nis not the composition it packs\n{}",
            store.proof_to_string(packed_proof),
            store.proof_to_string(chain_proof),
        );
    }

    /// A leaf proof of `lhs = rhs`, spelled the way an extracted `Fiat` row is.
    fn fiat_term(raw: &mut RawProofStore, lhs: TermId, rhs: TermId) -> TermId {
        let head = raw.names.fiat("Sort");
        raw.term_dag.app(head, vec![lhs, rhs])
    }

    /// A reflexive `Fiat` row over a nullary term, as an extracted proof term.
    fn leaf_proof_term(raw: &mut RawProofStore, name: &str) -> TermId {
        let value = raw.term_dag.app(name.to_string(), vec![]);
        fiat_term(raw, value, value)
    }

    /// An empty store whose names are the ones a packed row is spelled with.
    fn empty_store() -> RawProofStore {
        RawProofStore {
            term_dag: TermDag::default(),
            names: EncodingNames::new(&mut SymbolGen::new("test".to_string())),
            store: IndexSet::default(),
            term_to_proof: HashMap::default(),
        }
    }

    /// A packed row over `columns`, as the extracted term of the constructor
    /// carrying `skeleton`.
    fn packed_term(raw: &mut RawProofStore, skeleton: &Skeleton, columns: Vec<TermId>) -> TermId {
        assert!(
            skeleton.width() <= columns.len(),
            "one term per column the skeleton names"
        );
        let head = raw.names.packed_proof(columns.len());
        let spelling = raw.term_dag.lit(Literal::String(skeleton.spelling()));
        let args = std::iter::once(spelling).chain(columns).collect();
        raw.term_dag.app(head, args)
    }

    /// [`RawProofStore::from_extracted`]'s parse of one packed row.
    fn parse(raw: &mut RawProofStore, term: TermId) -> RawProofId {
        raw.parse_nested_first(term);
        raw.parse_proof(term)
    }

    /// A rebuild row's columns: the row proof, then each canonicalized column's
    /// step proof, then the e-class's own step when it has one.
    fn rebuild_columns(
        row: TermId,
        steps: &[(usize, TermId)],
        eclass: Option<TermId>,
    ) -> Vec<TermId> {
        let mut columns = vec![row];
        columns.extend(steps.iter().map(|&(_, step)| step));
        columns.extend(eclass);
        columns
    }

    /// One rebuild row, packed and parsed.
    fn rebuild(
        raw: &mut RawProofStore,
        row: TermId,
        steps: &[(usize, TermId)],
        eclass: Option<TermId>,
    ) -> RawProofId {
        let children: Vec<usize> = steps.iter().map(|&(child, _)| child).collect();
        let skeleton = rebuild_skeleton(&children, eclass.is_some());
        let columns = rebuild_columns(row, steps, eclass);
        let term = packed_term(raw, &skeleton, columns);
        parse(raw, term)
    }

    /// Columns 0 and 2 move, and so does the e-class; column 3's step is
    /// reflexive.
    #[test]
    fn rebuild_unpacks_to_the_chain_it_packs() {
        let mut firing = RebuildFiring::new();
        let (row, eclass) = (firing.row, firing.eclass);
        let steps = firing.steps.clone();
        let packed = rebuild(
            &mut firing.raw,
            row,
            &[(0, steps[0]), (2, steps[2]), (3, steps[3])],
            Some(eclass),
        );

        let row = firing.proof(row);
        let (step0, step2, step3) = (
            firing.proof(steps[0]),
            firing.proof(steps[2]),
            firing.proof(steps[3]),
        );
        let eclass = firing.proof(eclass);
        let at_0 = firing.raw.add_proof(RawProof::Congr(row, 0, step0));
        let at_2 = firing.raw.add_proof(RawProof::Congr(at_0, 2, step2));
        let at_3 = firing.raw.add_proof(RawProof::Congr(at_2, 3, step3));
        let back = firing.raw.add_proof(RawProof::Sym(eclass));
        let chain = firing.raw.add_proof(RawProof::Trans(back, at_3));

        let children = vec![firing.new[0], firing.old[1], firing.new[2], firing.old[3]];
        let expected = firing.concludes(firing.e_new, children);
        firing.assert_agree(packed, chain, &expected);
    }

    /// A view whose output is not an e-class: only child columns move.
    #[test]
    fn rebuild_without_an_eclass_step_unpacks_to_the_chain() {
        let mut firing = RebuildFiring::new();
        let row = firing.row;
        let steps = firing.steps.clone();
        let packed = rebuild(&mut firing.raw, row, &[(1, steps[1]), (3, steps[3])], None);

        let row = firing.proof(row);
        let (step1, step3) = (firing.proof(steps[1]), firing.proof(steps[3]));
        let at_1 = firing.raw.add_proof(RawProof::Congr(row, 1, step1));
        let chain = firing.raw.add_proof(RawProof::Congr(at_1, 3, step3));

        let children = vec![firing.old[0], firing.new[1], firing.old[2], firing.old[3]];
        let expected = firing.concludes(firing.e_old, children);
        firing.assert_agree(packed, chain, &expected);
    }

    /// Only the e-class moved, so the fold contributes nothing.
    #[test]
    fn rebuild_with_no_child_steps_unpacks_to_the_chain() {
        let mut firing = RebuildFiring::new();
        let (row, eclass) = (firing.row, firing.eclass);
        let packed = rebuild(&mut firing.raw, row, &[], Some(eclass));

        let row = firing.proof(row);
        let eclass = firing.proof(eclass);
        let back = firing.raw.add_proof(RawProof::Sym(eclass));
        let chain = firing.raw.add_proof(RawProof::Trans(back, row));

        let children = firing.old.clone();
        let expected = firing.concludes(firing.e_new, children);
        firing.assert_agree(packed, chain, &expected);
    }

    /// A rebuild lays out a column per canonicalizable column and then drops
    /// the steps that proved nothing, so the row carries columns its spelling
    /// never names.
    #[test]
    fn rebuild_reads_only_the_columns_its_spelling_names() {
        let mut firing = RebuildFiring::new();
        let (row, eclass) = (firing.row, firing.eclass);
        let steps = firing.steps.clone();
        // Columns 0 and 2 are laid out; column 2's step and the e-class's turn
        // out to be reflexive, so the spelling drops columns 2 and 3.
        let narrowed = rebuild_skeleton(&[0, 2], true)
            .without_column(2)
            .and_then(|skeleton| skeleton.without_column(3))
            .expect("the row proof still stands");
        let columns = rebuild_columns(row, &[(0, steps[0]), (2, steps[2])], Some(eclass));
        let term = packed_term(&mut firing.raw, &narrowed, columns);
        let packed = parse(&mut firing.raw, term);

        let row = firing.proof(row);
        let step0 = firing.proof(steps[0]);
        let chain = firing.raw.add_proof(RawProof::Congr(row, 0, step0));

        let children = vec![firing.new[0], firing.old[1], firing.old[2], firing.old[3]];
        let expected = firing.concludes(firing.e_old, children);
        firing.assert_agree(packed, chain, &expected);
    }

    /// The columns a narrowed spelling names need not be contiguous: a column
    /// dropped from the middle leaves the later ones where they were, since the
    /// row still carries it.
    #[test]
    fn rebuild_narrows_to_a_gap_in_its_columns() {
        let mut firing = RebuildFiring::new();
        let (row, eclass) = (firing.row, firing.eclass);
        let steps = firing.steps.clone();
        // Children 0 and 2 are laid out at columns 1 and 2; child 0's step turns
        // out to be reflexive, so the spelling names columns 0, 2 and 3 but not 1.
        let narrowed = rebuild_skeleton(&[0, 2], true)
            .without_column(1)
            .expect("the row proof still stands");
        assert_eq!(narrowed.spelling(), "trans_sym_p3_congr_p0_2_p2");
        let columns = rebuild_columns(row, &[(0, steps[0]), (2, steps[2])], Some(eclass));
        let term = packed_term(&mut firing.raw, &narrowed, columns);
        let packed = parse(&mut firing.raw, term);

        let row = firing.proof(row);
        let step2 = firing.proof(steps[2]);
        let eclass = firing.proof(eclass);
        let congr = firing.raw.add_proof(RawProof::Congr(row, 2, step2));
        let back = firing.raw.add_proof(RawProof::Sym(eclass));
        let chain = firing.raw.add_proof(RawProof::Trans(back, congr));

        let children = vec![firing.old[0], firing.old[1], firing.new[2], firing.old[3]];
        let expected = firing.concludes(firing.e_new, children);
        firing.assert_agree(packed, chain, &expected);
    }

    /// A step that names a child it does not start at is rejected rather than
    /// minting a proof of an equality nothing established.
    #[test]
    #[should_panic(expected = "congruence step 1 does not start at that child")]
    fn a_rebuild_step_at_the_wrong_child_is_rejected() {
        let mut firing = RebuildFiring::new();
        let (row, steps) = (firing.row, firing.steps.clone());
        let packed = rebuild(&mut firing.raw, row, &[(1, steps[0])], None);
        let mut store = ProofStore::new(
            firing.raw.term_dag.clone(),
            HashMap::default(),
            HashSet::default(),
        );
        store.convert_raw_proof(&vec![], &HashMap::default(), &firing.raw, packed);
    }

    /// Every column of the row is a proof, including the e-class's past the last
    /// step. A proof `nested_proofs` misses is still parsed, but by
    /// `parse_proof`'s recursion rather than by `parse_nested_first`'s heap
    /// stack, so a deep chain through it overflows.
    #[test]
    fn a_rebuild_rows_nested_proofs_are_its_row_and_its_steps() {
        let mut raw = empty_store();
        let row = leaf_proof_term(&mut raw, "row");
        let first = leaf_proof_term(&mut raw, "first");
        let second = leaf_proof_term(&mut raw, "second");
        let eclass = leaf_proof_term(&mut raw, "eclass");
        let steps = [(0, first), (2, second)];
        for (with_eclass, expected) in [
            (None, vec![row, first, second]),
            (Some(eclass), vec![row, first, second, eclass]),
        ] {
            let skeleton = rebuild_skeleton(&[0, 2], with_eclass.is_some());
            let columns = rebuild_columns(row, &steps, with_eclass);
            let term = packed_term(&mut raw, &skeleton, columns);
            assert_eq!(
                raw.nested_proofs(term),
                expected,
                "a rebuild row nests its row proof, its step proofs and its e-class proof"
            );
        }
    }

    /// A chain of rebuilds parses without recursing per link, on a stack far
    /// too small to hold one frame per link — through either proof field a link
    /// can chain on.
    #[test]
    fn a_deep_rebuild_chain_parses_without_a_deep_stack() {
        for through_eclass in [false, true] {
            std::thread::Builder::new()
                .stack_size(512 * 1024)
                .spawn(move || {
                    let mut raw = empty_store();
                    let step = leaf_proof_term(&mut raw, "step");
                    let leaf = leaf_proof_term(&mut raw, "row");
                    let skeleton = rebuild_skeleton(&[0], through_eclass);
                    let mut chain = leaf;
                    for _ in 0..50_000 {
                        let (row, eclass) = if through_eclass {
                            (leaf, Some(chain))
                        } else {
                            (chain, None)
                        };
                        let columns = rebuild_columns(row, &[(0, step)], eclass);
                        chain = packed_term(&mut raw, &skeleton, columns);
                    }
                    RawProofStore::from_extracted(&raw.names, raw.term_dag.clone(), chain);
                })
                .expect("spawn")
                .join()
                .expect("a deep rebuild chain should parse");
        }
    }

    /// The two compositions a merge collision packs, by which endpoint its two
    /// carried proofs share: the larger side's is column 0 and the smaller
    /// side's column 1, and whichever points the wrong way is reversed.
    fn displaced_skeletons() -> [Skeleton; 2] {
        [
            Skeleton::Leaf(0).sym().trans(Skeleton::Leaf(1)),
            Skeleton::Leaf(0).trans(Skeleton::Leaf(1).sym()),
        ]
    }

    /// One merge collision under `skeleton`: the larger side's carried proof,
    /// the smaller side's, and the `hi = lo` the displaced edge has to state.
    fn collision(raw: &mut RawProofStore, skeleton: &Skeleton) -> (TermId, TermId, Proposition) {
        let leaf = |raw: &mut RawProofStore, name: &str| raw.term_dag.app(name.into(), vec![]);
        let hi_term = leaf(raw, "hi");
        let lo_term = leaf(raw, "lo");
        let shared_term = leaf(raw, "shared");
        // The skeleton reverses whichever side does not already run `hi -> lo`.
        let shared_on_the_left =
            matches!(skeleton, Skeleton::Trans(left, _) if matches!(**left, Skeleton::Sym(_)));
        let (hi, lo) = if shared_on_the_left {
            (
                fiat_term(raw, shared_term, hi_term),
                fiat_term(raw, shared_term, lo_term),
            )
        } else {
            (
                fiat_term(raw, hi_term, shared_term),
                fiat_term(raw, lo_term, shared_term),
            )
        };
        (hi, lo, Proposition::new(hi_term, lo_term))
    }

    /// Either way the carried proofs point, the row unpacks to the `Sym` + `Trans`
    /// pair it packs, proving that the displaced side equals the kept one.
    #[test]
    fn displaced_unpacks_to_the_pair_it_packs() {
        for skeleton in displaced_skeletons() {
            let mut raw = empty_store();
            let (hi, lo, expected) = collision(&mut raw, &skeleton);
            let term = packed_term(&mut raw, &skeleton, vec![hi, lo]);
            let displaced = parse(&mut raw, term);
            let (hi, lo) = (raw.parse_proof(hi), raw.parse_proof(lo));
            let pair = match &skeleton {
                Skeleton::Trans(left, _) if matches!(**left, Skeleton::Sym(_)) => {
                    let back = raw.add_proof(RawProof::Sym(hi));
                    raw.add_proof(RawProof::Trans(back, lo))
                }
                _ => {
                    let back = raw.add_proof(RawProof::Sym(lo));
                    raw.add_proof(RawProof::Trans(hi, back))
                }
            };
            assert_agree(&raw, displaced, pair, &expected);
        }
    }

    /// Both carried proofs nest, so neither is left to `parse_proof`'s recursion
    /// (see [`a_rebuild_rows_nested_proofs_are_its_row_and_its_steps`]).
    #[test]
    fn a_displaced_rows_nested_proofs_are_its_two_carried_proofs() {
        let mut raw = empty_store();
        let hi = leaf_proof_term(&mut raw, "hi");
        let lo = leaf_proof_term(&mut raw, "lo");
        for skeleton in displaced_skeletons() {
            let term = packed_term(&mut raw, &skeleton, vec![hi, lo]);
            assert_eq!(
                raw.nested_proofs(term),
                vec![hi, lo],
                "a displaced row nests both carried proofs"
            );
        }
    }

    /// A chain of displaced edges — one collision's proof carried into the next —
    /// parses without recursing per link, on a stack far too small to hold one
    /// frame per link, through either carried proof.
    #[test]
    fn a_deep_displaced_chain_parses_without_a_deep_stack() {
        for skeleton in displaced_skeletons() {
            for through_lo in [false, true] {
                let skeleton = skeleton.clone();
                std::thread::Builder::new()
                    .stack_size(512 * 1024)
                    .spawn(move || {
                        let mut raw = empty_store();
                        let leaf = leaf_proof_term(&mut raw, "carried");
                        let mut chain = leaf;
                        for _ in 0..50_000 {
                            let columns = if through_lo {
                                vec![leaf, chain]
                            } else {
                                vec![chain, leaf]
                            };
                            chain = packed_term(&mut raw, &skeleton, columns);
                        }
                        RawProofStore::from_extracted(&raw.names, raw.term_dag.clone(), chain);
                    })
                    .expect("spawn")
                    .join()
                    .expect("a deep displaced chain should parse");
            }
        }
    }

    /// Every composition a packed row can stand for is recovered from the string
    /// the row carries, so the encoder and unpacking cannot drift apart.
    #[test]
    fn a_packed_rows_string_spells_its_skeleton() {
        let mut skeletons = displaced_skeletons().to_vec();
        for steps in 0..4 {
            for eclass in [false, true] {
                let children: Vec<usize> = (0..steps).map(|step| 2 * step).collect();
                skeletons.push(rebuild_skeleton(&children, eclass));
            }
        }
        for child in 0..3 {
            skeletons.push(Skeleton::Leaf(0).proj(child));
            skeletons.push(Skeleton::Leaf(0).congr(child, Skeleton::Leaf(0).proj(child)));
        }
        // A rebuild narrowed to a gapped set of columns, which is what a firing
        // whose middle column did not move writes.
        for dropped in 1..4 {
            skeletons.extend(rebuild_skeleton(&[0, 2, 4], true).without_column(dropped));
        }
        for skeleton in skeletons {
            let spelling = skeleton.spelling();
            assert_eq!(
                Skeleton::from_spelling(&spelling),
                Some(skeleton.clone()),
                "{spelling} should spell {skeleton:?}"
            );
        }
    }

    /// A store holding one `Fiat` over the term `f(a, b)`, treated as a value
    /// term so the checker accepts it, plus that proof's id.
    fn store_over_an_application() -> (ProofStore, ProofId, Vec<TermId>) {
        let mut term_dag = TermDag::default();
        let children: Vec<TermId> = ["a", "b"]
            .iter()
            .map(|name| term_dag.app((*name).to_string(), vec![]))
            .collect();
        let app = term_dag.app("f".to_string(), children.clone());
        let value_heads: HashSet<String> = ["f", "a", "b"].iter().map(|h| h.to_string()).collect();
        let mut store = ProofStore::new(term_dag, HashMap::default(), value_heads);
        let base = store.id_to_proof.push(Proof {
            proposition: Proposition::new(app, app),
            justification: Justification::Fiat,
        });
        (store, base, children)
    }

    /// A projection over a row's proof states — and checks as — the reflexivity
    /// of the child it names.
    #[test]
    fn a_projection_states_the_child_it_names() {
        for (child_index, child) in [0, 1].into_iter().zip(["(a)", "(b)"]) {
            let (mut store, base, children) = store_over_an_application();
            let proj = store.id_to_proof.push(Proof {
                proposition: Proposition::new(children[child_index], children[child_index]),
                justification: Justification::Proj {
                    proof: base,
                    child_index,
                },
            });
            let checked = store.check_proof(proj, &[]).expect("a valid projection");
            assert_eq!(
                store.term_dag.to_string(checked.lhs()),
                child,
                "projecting child {child_index} proves that child reflexive"
            );
            assert_eq!(checked.lhs(), checked.rhs());
        }
    }

    /// The checker rejects a projection whose conclusion is not the named
    /// child's reflexivity, and one whose index the term has no child at.
    #[test]
    fn a_projection_of_the_wrong_child_is_rejected() {
        let (mut store, base, children) = store_over_an_application();
        let wrong = store.id_to_proof.push(Proof {
            proposition: Proposition::new(children[1], children[1]),
            justification: Justification::Proj {
                proof: base,
                child_index: 0,
            },
        });
        let err = store.check_proof(wrong, &[]).unwrap_err().to_string();
        assert!(
            err.contains("projection error"),
            "the wrong child should be a projection error, got {err}"
        );

        let out_of_range = store.id_to_proof.push(Proof {
            proposition: Proposition::new(children[0], children[0]),
            justification: Justification::Proj {
                proof: base,
                child_index: 2,
            },
        });
        let err = store
            .check_proof(out_of_range, &[])
            .unwrap_err()
            .to_string();
        assert!(
            err.contains("child index 2 out of bounds"),
            "an out-of-range index should say so, got {err}"
        );

        let literal = store.term_dag.lit(Literal::Int(1));
        let over_a_literal = store.id_to_proof.push(Proof {
            proposition: Proposition::new(literal, literal),
            justification: Justification::Fiat,
        });
        let not_an_app = store.id_to_proof.push(Proof {
            proposition: Proposition::new(literal, literal),
            justification: Justification::Proj {
                proof: over_a_literal,
                child_index: 0,
            },
        });
        let err = store.check_proof(not_an_app, &[]).unwrap_err().to_string();
        assert!(
            err.contains("not a function application"),
            "a literal has no child to project, got {err}"
        );
    }

    /// A packed row spelling a projection unpacks to it, over the child the
    /// spelling names.
    #[test]
    fn a_projection_row_unpacks_to_the_projection_it_packs() {
        let mut raw = empty_store();
        let children: Vec<TermId> = ["a", "b", "c"]
            .iter()
            .map(|name| raw.term_dag.app((*name).to_string(), vec![]))
            .collect();
        let app = raw.term_dag.app("f".to_string(), children.clone());
        let row = fiat_term(&mut raw, app, app);

        let skeleton = Skeleton::Leaf(0).proj(1);
        let term = packed_term(&mut raw, &skeleton, vec![row]);
        let packed = parse(&mut raw, term);

        let row = raw.parse_proof(row);
        let chain = raw.add_proof(RawProof::Proj(row, 1));
        let expected = Proposition::new(children[1], children[1]);
        assert_agree(&raw, packed, chain, &expected);
    }

    /// A projection naming its child by term converts to the projection at the
    /// position that term occupies, and the two share one proof.
    #[test]
    fn an_element_projection_is_the_positional_one_over_the_same_child() {
        let mut raw = empty_store();
        let children: Vec<TermId> = ["a", "b", "c"]
            .iter()
            .map(|name| raw.term_dag.app((*name).to_string(), vec![]))
            .collect();
        let app = raw.term_dag.app("f".to_string(), children.clone());
        let row = fiat_term(&mut raw, app, app);
        let row = raw.parse_proof(row);

        let by_term = raw.add_proof(RawProof::ProjAll(row, children[1]));
        let by_index = raw.add_proof(RawProof::Proj(row, 1));

        let mut store =
            ProofStore::new(raw.term_dag.clone(), HashMap::default(), HashSet::default());
        let (prog, globals) = (vec![], HashMap::default());
        let mut convert = |id| store.convert_raw_proof(&prog, &globals, &raw, id);
        let (element, positional) = (convert(by_term), convert(by_index));
        assert_eq!(
            element, positional,
            "the element projection should resolve to the positional one it desugars to"
        );
        assert_eq!(
            store.get(element).proposition(),
            &Proposition::new(children[1], children[1])
        );
    }
}
