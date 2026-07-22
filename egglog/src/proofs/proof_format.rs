use crate::{
    ResolvedCall, Term, TermDag, TermId,
    ast::{FunctionSubtype, GenericNCommand, ResolvedExpr, ResolvedFact, ResolvedNCommand},
    proofs::{
        proof_checker::{
            ProofCheckError, ProofCheckErrorKind, eval_expr_with_subst, gather_globals, run_merge,
        },
        proof_encoding_helpers::EncodingNames,
    },
    typechecking::{FuncType, PrimitiveValidator},
    util::{HEntry, HashMap, HashSet, IndexSet, SymbolGen},
};
use egglog_ast::generic_ast::Literal;
use egglog_numeric_id::{DenseIdMap, NumericId, define_id};
use std::fmt;

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

/// A proof straight from the e-graph, not exposed to users.
struct RawProofStore {
    term_dag: TermDag,
    /// The proof constructor names, used to recognize each extracted proof
    /// term's head by exact match (rather than substring guessing).
    names: EncodingNames,
    /// Bidirectional map between proof terms and their ids.
    store: IndexSet<RawProof>,
    term_to_proof: HashMap<TermId, RawProofId>,
    proof_to_term: HashMap<RawProofId, TermId>,
}

pub(crate) fn proof_store_from_term(
    encoding_names: &EncodingNames,
    term_dag: TermDag,
    proof_term: TermId,
    prog: &Vec<ResolvedNCommand>,
    container_normalizers: HashMap<String, PrimitiveValidator>,
    primitive_validators: HashMap<String, Vec<PrimitiveValidator>>,
) -> (ProofStore, ProofId) {
    let (raw_store, raw_proof_id) =
        RawProofStore::from_extracted(encoding_names, term_dag, proof_term);
    ProofStore::from_raw(
        prog,
        raw_store,
        raw_proof_id,
        container_normalizers,
        primitive_validators,
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
    /// Given a rule name and proofs for each premise, produces a proof of a grounded equality t1 = t2 from the body of the rule.
    /// The subsitution is implicit- in [`ProofTerm`] they are explicit.
    Rule(String, Vec<RawProofId>, TermId, TermId),
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
    /// Primitive name -> the validators of its overloads, used to accept a
    /// reflexive `Fiat` over a primitive-built term by re-evaluation
    /// ([`ProofStore::reflexive_primitive_term`]).
    primitive_validators: HashMap<String, Vec<PrimitiveValidator>>,
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
/// Compared to [`RawProof`], a [`Justification`] is always paired with the [`Proposition`] being proven (in a [`Proof`]).
/// Additionally, [`Justification::Rule`] includes the explicit substitution mapping variable names to terms,
/// while [`RawProof::Rule`] leaves this implicit.
#[derive(Clone, Debug)]
pub enum Justification {
    /// Equalities added at the top level are justified by fiat.
    /// Primitive reflexive equalities like 2 = 2 are also justified by Fiat.
    /// Reflexivity of equality is not assumed: a proof of `t = t`` must correspond to some `t` added at the top level.
    Fiat,
    /// Proves a grounded equality `t1 = t2` which appears
    /// in the body of a rule given a substitution given proofs
    /// for each premise ([`Fact`]) of the rule.
    /// If the [`Propostion`] proven is a term like `t = t`,
    /// t may be a subexpression of the body of the rule under the substitution.
    ///
    /// A proof for a premise is an equality t1 = t2 that matches the premise under some substitution.
    /// A proof for a premise that doesn't involve equality (i.e. (Add a b)) gives a proof of t1 = t2 where t2 matches the premise.
    /// A proof for a premise about a funciton (= (f a b ...) c) gives a proof (f a b ... c) = (f a b ... c).
    Rule {
        name: String,
        premise_proofs: Vec<ProofId>,
        substitution: HashMap<String, TermId>,
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
            proof_to_term: HashMap::default(),
        };
        let parsed = store.parse_proof(term);
        (store, parsed)
    }

    fn parse_proof(&mut self, term_id: TermId) -> RawProofId {
        if let Some(&proof_id) = self.term_to_proof.get(&term_id) {
            return proof_id;
        }

        let proof_id = self.parse_proof_inner(term_id);
        self.term_to_proof.insert(term_id, proof_id);
        self.proof_to_term.insert(proof_id, term_id);
        proof_id
    }

    fn parse_proof_inner(&mut self, term_id: TermId) -> RawProofId {
        let term = self.term_dag.get(term_id).clone();
        let Term::App(head, args) = term else {
            panic!(
                "Expected proof term to be an app, got {term:?}. Proof parsing assumes valid proofs."
            );
        };

        let proof = if head == self.names.fiat_constructor {
            assert!(args.len() == 2, "fiat constructor should have 2 args");
            RawProof::Fiat(args[0], args[1])
        } else if head == self.names.rule_constructor {
            assert!(args.len() == 4, "rule constructor should have 4 args");
            let name = self.parse_string(args[0]);
            let premises = self.parse_proof_list(args[1]);
            RawProof::Rule(name, premises, args[2], args[3])
        } else if head == self.names.merge_fn_idx_constructor {
            assert!(args.len() == 4, "merge-idx constructor should have 4 args");
            let function = self.parse_string(args[0]);
            let old_proof = self.parse_proof(args[1]);
            let new_proof = self.parse_proof(args[2]);
            let idx = self.parse_index(args[3]);
            RawProof::MergeFnIdx(function, old_proof, new_proof, idx)
        } else if head == self.names.merge_fn_row_constructor {
            assert!(args.len() == 3, "merge-row constructor should have 3 args");
            let function = self.parse_string(args[0]);
            let old_proof = self.parse_proof(args[1]);
            let new_proof = self.parse_proof(args[2]);
            RawProof::MergeFnRow(function, old_proof, new_proof)
        } else if head == self.names.eq_trans_constructor {
            assert!(args.len() == 2, "trans constructor should have 2 args");
            let left = self.parse_proof(args[0]);
            let right = self.parse_proof(args[1]);
            RawProof::Trans(left, right)
        } else if head == self.names.eq_sym_constructor {
            assert!(args.len() == 1, "sym constructor should have 1 arg");
            let inner = self.parse_proof(args[0]);
            RawProof::Sym(inner)
        } else if head == self.names.container_normalize_constructor {
            assert!(
                args.len() == 1,
                "container-normalize constructor should have 1 arg"
            );
            let inner = self.parse_proof(args[0]);
            RawProof::ContainerNormalize(inner)
        } else if head == self.names.congr_constructor {
            assert!(args.len() == 3, "congr constructor should have 3 args");
            let proof = self.parse_proof(args[0]);
            let child_index = self.parse_index(args[1]);
            let child_proof = self.parse_proof(args[2]);
            RawProof::Congr(proof, child_index, child_proof)
        } else if head == self.names.congr_all_constructor {
            assert!(args.len() == 2, "congr-all constructor should have 2 args");
            let proof = self.parse_proof(args[0]);
            let child_proof = self.parse_proof(args[1]);
            RawProof::CongrAll(proof, child_proof)
        } else if head == self.names.eval_constructor {
            assert!(args.is_empty(), "eval constructor should have no args");
            RawProof::Eval
        } else {
            panic!("Unrecognized proof term head: {head}. Proof parsing assumes valid proofs.");
        };

        self.add_proof(proof)
    }

    fn parse_proof_list(&mut self, list_term: TermId) -> Vec<RawProofId> {
        let term = self.term_dag.get(list_term).clone();
        match term {
            Term::App(head, args) => {
                if head == self.names.pnil {
                    assert!(args.is_empty(), "pnil should not have arguments");
                    Vec::new()
                } else if head == self.names.pcons {
                    assert!(args.len() == 2, "pcons should have 2 arguments");
                    let head_proof = self.parse_proof(args[0]);
                    let rest = self.parse_proof_list(args[1]);
                    let mut list = Vec::with_capacity(rest.len() + 1);
                    list.push(head_proof);
                    list.extend(rest);
                    list
                } else {
                    panic!(
                        "expected proof list constructor, got {head}. Proof parsing assumes valid proofs."
                    );
                }
            }
            other => {
                panic!("expected proof list, got {other:?}. Proof parsing assumes valid proofs.")
            }
        }
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

    fn add_proof(&mut self, proof: RawProof) -> RawProofId {
        if let Some(id) = self.store.get_index_of(&proof) {
            return RawProofId::from_usize(id);
        }
        self.store.insert(proof);
        RawProofId::from_usize(self.store.len() - 1)
    }

    fn unwrap_ast(&self, term_id: TermId) -> TermId {
        let term = self.term_dag.get(term_id).clone();
        let Term::App(_, args) = term else {
            panic!("expected ast wrapper application");
        };
        assert!(
            args.len() == 1,
            "ast wrapper should have exactly one child, got {}",
            args.len()
        );
        args[0]
    }
}

/// True iff `fact` is a custom-function application fact `(= (f args) v)` (either
/// argument order), for which the checker's proof normal form expects a *reflexive*
/// premise proof. Constructor and plain equality facts are excluded.
fn is_custom_func_fact(fact: &ResolvedFact) -> bool {
    let call = match fact {
        ResolvedFact::Eq(_, ResolvedExpr::Call(_, c, _), ResolvedExpr::Var(..))
        | ResolvedFact::Eq(_, ResolvedExpr::Var(..), ResolvedExpr::Call(_, c, _)) => c,
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

    /// Whether `term` is a primitive-closed computation the checker can
    /// re-evaluate from the term alone: a literal, or an application of a
    /// registered primitive (any overload) to primitive-closed arguments whose
    /// validator reproduces exactly this term. A reflexive `Fiat` over such a
    /// term is self-evident.
    pub(super) fn reflexive_primitive_term(&mut self, term: TermId) -> bool {
        match self.term_dag.get(term).clone() {
            Term::Lit(_) => true,
            Term::Var(_) => false,
            Term::App(head, args) => {
                let Some(validators) = self.primitive_validators.get(&head).cloned() else {
                    return false;
                };
                if !args.iter().all(|a| self.reflexive_primitive_term(*a)) {
                    return false;
                }
                validators
                    .iter()
                    .any(|v| v(&mut self.term_dag, &args) == Some(term))
            }
        }
    }

    /// Get the [`Proof`] with the given id.
    /// Panics if the id is invalid (if it came from another proof store, for example).
    pub fn get(&self, proof_id: ProofId) -> &Proof {
        &self.id_to_proof[proof_id]
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

    fn from_raw(
        prog: &Vec<ResolvedNCommand>,
        raw_store: RawProofStore,
        raw_proof_id: RawProofId,
        container_normalizers: HashMap<String, PrimitiveValidator>,
        primitive_validators: HashMap<String, Vec<PrimitiveValidator>>,
    ) -> (ProofStore, ProofId) {
        let mut store = ProofStore {
            term_dag: raw_store.term_dag.clone(),
            proof_id: HashMap::default(),
            id_to_proof: DenseIdMap::new(),
            container_normalizers,
            primitive_validators,
        };
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
        let prop = self.id_to_proof[premise_id].proposition.clone();
        if prop.lhs == prop.rhs {
            return premise_id;
        }
        // Sym(p) : rhs = lhs
        let sym_id = self.id_to_proof.push(Proof {
            proposition: Proposition::new(prop.rhs, prop.lhs),
            justification: Justification::Sym(premise_id),
        });
        // Trans(Sym(p), p) : rhs = rhs
        self.id_to_proof.push(Proof {
            proposition: Proposition::new(prop.rhs, prop.rhs),
            justification: Justification::Trans(sym_id, premise_id),
        })
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
                proposition: Proposition::new(
                    raw_store.unwrap_ast(*lhs),
                    raw_store.unwrap_ast(*rhs),
                ),
                justification: Justification::Fiat,
            },
            RawProof::Rule(name, premise_proofs, lhs, rhs) => {
                let converted_premises: Vec<ProofId> = premise_proofs
                    .iter()
                    .map(|pid| self.convert_raw_proof(prog, globals, raw_store, *pid))
                    .collect();

                // Rebuild/canonicalization can rewrite a matched custom-function-fact
                // premise `(= (f args) v)` into a non-reflexive natural->canonical
                // `Congr` proof `(f nat) = (f canon)` (e.g. when an argument's e-class
                // has several equivalent shapes from commutativity/associativity
                // rewrites). The checker's function-fact normal form expects a
                // reflexive premise at the matched (canonical) shape, so reflexivize
                // those. Equality-fact premises `(= a b)` must stay non-reflexive.
                let reflex_mask: Vec<bool> = {
                    let rule = prog
                        .iter()
                        .find_map(|cmd| match cmd {
                            ResolvedNCommand::NormRule { rule } if rule.name == *name => Some(rule),
                            _ => None,
                        })
                        .unwrap_or_else(|| panic!("could not find rule with name {name}"));
                    rule.body.iter().map(is_custom_func_fact).collect()
                };
                // Premises are in body-fact order, one per fact (the checker rejects
                // any count mismatch), so zip pairs each with its fact's decision.
                let converted_premises: Vec<ProofId> = converted_premises
                    .into_iter()
                    .zip(reflex_mask)
                    .map(|(pid, reflex)| {
                        if reflex {
                            self.reflexivize_premise(pid)
                        } else {
                            pid
                        }
                    })
                    .collect();

                let mut substitution =
                    self.compute_rule_substitution(prog, name, &converted_premises);
                // remove globals from the substitution, since they are not necessary
                substitution.retain(|var, _term_id| globals.get(var).is_none());

                Proof {
                    proposition: Proposition::new(
                        raw_store.unwrap_ast(*lhs),
                        raw_store.unwrap_ast(*rhs),
                    ),
                    justification: Justification::Rule {
                        name: name.clone(),
                        premise_proofs: converted_premises,
                        substitution,
                    },
                }
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

    /// For a given rule and premise proofs, compute the substitution used in the rule application.
    /// The proof has enough information to compute the substitution, we do it here
    /// for convenience.
    fn compute_rule_substitution(
        &self,
        prog: &[ResolvedNCommand],
        rule_name: &str,
        premise_proofs: &[ProofId],
    ) -> HashMap<String, TermId> {
        let substitution = HashMap::default();

        let Some(rule) = prog.iter().find_map(|cmd| match cmd {
            ResolvedNCommand::NormRule { rule } if rule.name == rule_name => Some(rule),
            _ => None,
        }) else {
            panic!("could not find rule with name {rule_name}");
        };

        if rule.body.len() != premise_proofs.len() {
            panic!(
                "rule {} has {} premises, but got {} premise proofs",
                rule_name,
                rule.body.len(),
                premise_proofs.len()
            );
        }

        let mut current_subst = substitution;
        for (fact, proof_id) in rule.body.iter().zip(premise_proofs.iter()) {
            // Container side conditions carry only an `Eval` marker (no value);
            // their bindings are generated by `check_side_condition` at check
            // time, so there is nothing to unify here.
            if crate::proofs::proof_checker::is_container_side_condition(fact) {
                continue;
            }
            self.unify_fact(fact, *proof_id, &mut current_subst);
        }

        current_subst
    }

    fn unify_fact(
        &self,
        fact: &ResolvedFact,
        proof_id: ProofId,
        subst: &mut HashMap<String, TermId>,
    ) {
        let proof = &self.id_to_proof[proof_id];
        match fact {
            // In proof normal form, this is the only way that function calls apppear.
            ResolvedFact::Eq(
                _span,
                ResolvedExpr::Call(
                    _span2,
                    head @ ResolvedCall::Func(FuncType {
                        subtype: FunctionSubtype::Custom,
                        ..
                    }),
                    args,
                ),
                ResolvedExpr::Var(_span3, v),
            ) => {
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

                // bind last child to v
                let var_child_term = children.last().unwrap();
                self.add_to_subst(subst, &v.name, *var_child_term);
                // unify other args
                for (arg_expr, child_term) in args.iter().zip(children.iter()) {
                    self.unify_expr(arg_expr, *child_term, subst);
                }
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

    fn add_to_subst(&self, subst: &mut HashMap<String, TermId>, var: &str, term_id: TermId) {
        match subst.entry(var.to_string()) {
            HEntry::Vacant(entry) => {
                entry.insert(term_id);
            }
            HEntry::Occupied(entry) => {
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
        substitution: &mut HashMap<String, TermId>,
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
                "Fiat" | "Rule" | "Merge" | "Trans" | "Sym" | "Congr" | "ContainerNormalize"
                | "Eval" => "prf".to_string(),
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
