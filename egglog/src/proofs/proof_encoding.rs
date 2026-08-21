#[doc = include_str!("proof_encoding.md")]
use crate::proofs::proof_encoding_helpers::{
    Composition, EncodingNames, HeadColumn, Justification, Skeleton,
};
use crate::proofs::proof_head::{
    Head, HeadPlan, HeadPosition, HeadProof, HeadRun, ProofAlgebra, constructor_operand,
};
use crate::typechecking::FuncType;
use crate::*;

/// A value an instrumented action names: the id later statements read it by
/// and, for a term the encoding built here, the term as written plus the proof
/// connecting the two.
///
/// A proof about the term's shape has to be stated over the natural form, since
/// the id is an interned e-class whose term may float.
#[derive(Clone)]
pub(crate) struct Operand {
    /// The id later statements read this operand by.
    value: String,
    /// The term as written; the same id unless the encoding built it here.
    natural: String,
    /// `natural = value`, `None` when the two are the same id.
    connector: Option<Connector>,
}

impl Operand {
    /// An operand the encoding did not build here: a literal, a body match, a
    /// value read out of a view.
    fn plain(value: String) -> Self {
        Operand {
            natural: value.clone(),
            value,
            connector: None,
        }
    }

    /// A term the encoding built as `natural` and interned into `value`.
    fn built(value: String, natural: String, connector: Connector) -> Self {
        Operand {
            value,
            natural,
            connector: Some(connector),
        }
    }
}

/// The ids emitted code reads a run of operands by.
fn ids(operands: &[Operand]) -> Vec<String> {
    operands.iter().map(|o| o.value.clone()).collect()
}

/// A `union`'s two endpoints in the order its `@UF` row uses them: the larger,
/// which keys the row, and the smaller, which the row points at.
fn ordered_endpoints(lhs: &Operand, rhs: &Operand) -> (String, String) {
    (
        format!("(ordering-max {} {})", lhs.value, rhs.value),
        format!("(ordering-min {} {})", lhs.value, rhs.value),
    )
}

/// What justifies the rows of the `idx`th subexpression of `fname`'s merge body
/// (see [`ProofInstrumentor::instrument_merge_body`]).
fn merge_idx(fname: &str, idx: usize) -> Justification {
    Justification::MergeIdx(
        fname.to_string(),
        "old1".to_string(),
        "new1".to_string(),
        idx,
    )
}

/// The column of `run` holding `proof`. Unnumbered where the site composes
/// rather than claiming a run.
fn head_column(run: Option<HeadRun>, proof: HeadProof) -> HeadColumn {
    run.map_or(HeadColumn::Unnumbered, |run| {
        HeadColumn::Numbered(run.column(proof).to_string())
    })
}

/// The variables an action block has bound to a term the encoding built. Every
/// other name reads back as itself, so only these are recorded.
#[derive(Default)]
struct Scope(HashMap<String, Operand>);

impl Scope {
    /// What `name` stands for.
    fn read(&self, name: &str) -> Operand {
        self.0
            .get(name)
            .cloned()
            .unwrap_or_else(|| Operand::plain(name.to_string()))
    }

    /// Record that `(let name <operand>)` was emitted, so a later reference to
    /// `name` reads the same term.
    fn bind(&mut self, name: &str, operand: &Operand) {
        if operand.connector.is_some() {
            self.0.insert(
                name.to_string(),
                Operand {
                    value: name.to_string(),
                    ..operand.clone()
                },
            );
        }
    }
}

/// Where the encoder is writing: the statements it appends to, the head those
/// statements belong to, and what justifies the rows they mint.
struct Emit<'a> {
    stmts: &'a mut Vec<String>,
    head: &'a mut Head,
    justification: &'a Justification,
}

impl<'a> Emit<'a> {
    /// The same place, writing rows `justification` justifies instead — a
    /// numbered column of the same rule, or a proof composed on the spot.
    fn justified_by<'b>(&'b mut self, justification: &'b Justification) -> Emit<'b> {
        Emit {
            stmts: &mut *self.stmts,
            head: &mut *self.head,
            justification,
        }
    }

    /// Write at a position the head concludes nothing about, per
    /// [`Head::composing`].
    fn composing<R>(&mut self, lower: impl FnOnce(&mut Emit) -> R) -> R {
        let Emit {
            stmts,
            head,
            justification,
        } = self;
        let justification = *justification;
        head.composing(|head| {
            lower(&mut Emit {
                stmts,
                head,
                justification,
            })
        })
    }
}

/// How a built term's connector proof `natural = canonical` is named.
#[derive(Clone)]
pub(crate) enum Connector {
    /// A proof node the encoding already minted.
    Node(String),
    /// A rule head's, named by the column of the head's proof (see
    /// [`crate::proofs::proof_head`]), so a row is minted only where the encoding
    /// stores the proof.
    Column(usize),
}

/// A constructor's *natural* node — children at their as-built ids — and the
/// proofs about it. Shared by [`ProofInstrumentor::add_constructor_with_proof`]
/// and [`ProofInstrumentor::instrument_construct_into`].
struct Natural {
    /// The children at their deduped ids, the view's key.
    dedup_args: Vec<String>,
    /// The natural node's id.
    fv_nat: String,
    /// `fv_nat = f(deduped children)`: one `Congr` per canonicalized child.
    /// `None` in a rule head, where proof conversion folds it instead.
    to_dedup: Option<String>,
}

/// A declared index on a function's view, covering the view columns of one
/// eq-sort — its children and its e-class. An `@UF` edge on a term reaches every
/// row mentioning it at any of them.
#[derive(Clone)]
pub(crate) struct ViewIndex {
    pub name: String,
    pub sort_name: String,
}

// TODO refactor so that encoding state is optional on the e-graph, ProofNames not optional on EncodingState. Then we don't have to clone proof names everywhere.
#[derive(Clone)]
pub(crate) struct EncodingState {
    pub uf_parent: HashMap<String, String>,
    /// Maps container sort name -> the name of its registered container-rebuild
    /// primitive (`ContainerRebuild`). Cached so each container sort gets
    /// a single rebuild primitive shared across all functions using it.
    pub container_rebuild_name: HashMap<String, String>,
    /// Maps container sort name -> the name of its registered proof-producing
    /// container-rebuild primitive (`ContainerRebuildProof`). Proof mode only.
    pub container_rebuild_proof_name: HashMap<String, String>,
    /// Function name -> the rebuild indexes declared on its view, one per
    /// distinct eq-sort among the view's columns (see [`ViewIndex`]).
    pub view_index: HashMap<String, Vec<ViewIndex>>,
    pub term_header_added: bool,
    // TODO this is very ugly- we should separate out a typechecking struct
    // since we didn't need an entire e-graph
    // When Some term encoding is enabled.
    pub original_typechecking: Option<Box<EGraph>>,
    pub proofs_enabled: bool,
    pub proof_testing: bool,
    /// Whether extracted proofs are verified.
    pub verify_proofs: bool,
    pub proof_names: EncodingNames,
    /// Test-only knob: annotate RHS-reading rules `:naive` (the safe
    /// whole-database baseline) instead of `:unsafe-seminaive`, so tests can
    /// assert the two produce the same database.
    pub force_proof_naive: bool,
}

impl EncodingState {
    pub(crate) fn new(symbol_gen: &mut SymbolGen) -> Self {
        Self {
            uf_parent: HashMap::default(),
            container_rebuild_name: HashMap::default(),
            container_rebuild_proof_name: HashMap::default(),
            view_index: HashMap::default(),
            term_header_added: false,
            original_typechecking: None,
            proofs_enabled: false,
            proof_names: EncodingNames::new(symbol_gen),
            proof_testing: false,
            verify_proofs: true,
            force_proof_naive: false,
        }
    }
}

/// Thin wrapper around an [`EGraph`] for the term encoding
pub(crate) struct ProofInstrumentor<'a> {
    pub(crate) egraph: &'a mut EGraph,
    /// Proof variables the encoder knows prove `t = t`, keyed by the emitted
    /// variable name. Names are globally fresh, so entries never collide across
    /// the generated programs.
    reflexive: HashSet<String>,
    /// What each proof still held back binds, keyed by its variable. A proof is
    /// written where it is first read; one nothing reads is never written at all.
    deferred: HashMap<String, Deferred>,
    /// Compositions that get a row of their own rather than being written into
    /// the one composing over them (see [`Self::level_connector`]).
    sealed: HashSet<String>,
    /// Declarations the statements written so far need — packed proof
    /// constructors and subsumption scaffolding — to be emitted ahead of the
    /// command using them.
    pending_decls: Vec<String>,
    /// The body anchors of the query being instrumented (see [`BodyAnchors`]).
    anchors: BodyAnchors,
    /// Anchor requests no body atom could reach, as proof variable and the
    /// value variable asked about. Reading one is an error.
    unanchored: HashMap<String, String>,
}

/// Where a variable a rule body binds gets its reflexive `t = t` proof from: a
/// view atom's row proof states an equality whose right-hand side is the row's
/// term, so every variable that term mentions is reachable from it.
#[derive(Clone, Copy)]
pub(crate) enum Anchor {
    /// The variable is the row term's child at this position.
    Child(usize),
    /// The variable is the row proof's left-hand side.
    Lhs,
}

/// A value a body primitive read out of a container. Nothing in the query names
/// it as a term, but it is a child of whichever of `containers` it came out of,
/// so an anchor for one of those projects it out by term.
#[derive(Clone)]
struct Element {
    containers: Vec<String>,
    /// The value variable the projection anchoring it names.
    value: String,
    /// The variable holding the name of the rule whose body read the element.
    rule_name: String,
    /// The reading call's index in the rule body's
    /// [`body_exprs`](crate::proofs::proof_encoding_helpers::body_exprs): how
    /// proof conversion recovers the resolved primitive, which a name alone
    /// could not, since primitives are overloaded.
    body_index: usize,
    /// One proof per argument of the reading call, in order, with the container
    /// argument left empty — the anchor chain resolves that one, so it is only
    /// known once the whole body is walked.
    arg_proofs: Vec<Option<String>>,
    /// Which argument the container is.
    container_index: usize,
}

/// What a body variable's anchor is projected out of.
enum Source {
    /// A view row proof the body reads, which mentions the variable's term.
    Row(String, Anchor),
    /// A container the body read the variable out of.
    Element(Element),
}

/// The reflexive anchors one rule body offers, collected while its facts are
/// instrumented and read once the whole body is walked — a variable's anchor may
/// come from a fact later than the one asking for it.
#[derive(Default)]
pub(crate) struct BodyAnchors {
    /// Value variable -> the row proof it is reachable from, and how.
    supply: HashMap<String, (String, Anchor)>,
    /// Value variable -> the containers it was read out of.
    elements: HashMap<String, Element>,
    /// Value variables the body forces to be equal, so either one's anchor
    /// proves the other reflexive.
    aliases: Vec<(String, String)>,
    /// Anchors asked for, as proof variable and the value it is about.
    requests: Vec<(String, String)>,
}

impl BodyAnchors {
    /// Record that `row_proof`'s equality reaches `value` at `anchor`. The first
    /// atom binding a variable wins; a later one says the same thing.
    fn offer(&mut self, value: &str, row_proof: &str, anchor: Anchor) {
        self.supply
            .entry(value.to_string())
            .or_insert_with(|| (row_proof.to_string(), anchor));
    }

    /// Record that a body primitive read `element` out of a container.
    fn offer_element(&mut self, element: Element) {
        self.elements
            .entry(element.value.clone())
            .or_insert(element);
    }

    /// Record that the body only matches when `left` and `right` hold the same
    /// value, so one anchor serves both.
    fn alias(&mut self, left: &str, right: &str) {
        self.aliases.push((left.to_string(), right.to_string()));
    }

    /// Ask for `value`'s anchor, to be bound to the proof variable `proof`.
    fn request(&mut self, proof: &str, value: &str) {
        self.requests.push((proof.to_string(), value.to_string()));
    }

    /// Where `value`'s anchor comes from, following the body's aliases when the
    /// variable itself is not one an atom reaches. A row proof wins over a
    /// container projection.
    fn resolve(&self, value: &str) -> Option<Source> {
        let mut seen: HashSet<&str> = HashSet::default();
        let mut reached: Vec<&str> = vec![];
        let mut frontier = vec![value];
        while let Some(var) = frontier.pop() {
            if !seen.insert(var) {
                continue;
            }
            reached.push(var);
            for (left, right) in &self.aliases {
                if left == var {
                    frontier.push(right);
                } else if right == var {
                    frontier.push(left);
                }
            }
        }
        let row = reached.iter().find_map(|var| {
            let (row_proof, anchor) = self.supply.get(*var)?;
            Some(Source::Row(row_proof.clone(), *anchor))
        });
        row.or_else(|| {
            reached
                .iter()
                .find_map(|var| Some(Source::Element(self.elements.get(*var)?.clone())))
        })
    }

    /// How `value`'s anchor is reached: the row proof it bottoms out in and how
    /// that row mentions its term, plus the container projections leading back
    /// to `value`, outermost container first.
    fn anchor_chain(&self, value: &str) -> Option<(String, Anchor, Vec<Element>)> {
        match self.resolve(value)? {
            Source::Row(row_proof, anchor) => Some((row_proof, anchor, vec![])),
            Source::Element(element) => {
                let (row_proof, anchor, mut chain) = element
                    .containers
                    .iter()
                    .find_map(|container| self.anchor_chain(container))?;
                chain.push(element);
                Some((row_proof, anchor, chain))
            }
        }
    }
}

/// A held-back proof: finished statements, emitted as they stand (see
/// [`ProofInstrumentor::defer_lookup`]), or a composition the encoder can still
/// rewrite into one row (see [`ProofInstrumentor::mint_sym`]).
enum Deferred {
    /// Finished statements, together with the proof variables they read. Those
    /// groups are emitted first, so a group may be held back before the ones it
    /// stands on are.
    Stmts {
        stmts: Vec<String>,
        reads: Vec<String>,
    },
    Composed(Composition),
}

/// The variables a joined argument string names: its whitespace-separated
/// tokens, with any wrapping parentheses stripped so a primitive call reads as
/// the variables inside it.
fn read_vars(args_joined: &str) -> impl Iterator<Item = &str> {
    args_joined
        .split_whitespace()
        .map(|arg| arg.trim_matches(|c| c == '(' || c == ')'))
}

impl<'a> ProofInstrumentor<'a> {
    pub(crate) fn new(egraph: &'a mut EGraph) -> Self {
        Self {
            egraph,
            reflexive: HashSet::default(),
            deferred: HashMap::default(),
            sealed: HashSet::default(),
            pending_decls: vec![],
            anchors: BodyAnchors::default(),
            unanchored: HashMap::default(),
        }
    }

    /// Make a term state and use it to instrument the code.
    pub(crate) fn add_term_encoding(
        egraph: &'a mut EGraph,
        program: Vec<ResolvedNCommand>,
    ) -> Result<Vec<Command>, Error> {
        Self::new(egraph).add_term_encoding_helper(program)
    }

    pub(crate) fn lower_inputs(
        egraph: &EGraph,
        program: Vec<ResolvedNCommand>,
    ) -> Result<Vec<ResolvedNCommand>, Error> {
        let mut lowered = Vec::with_capacity(program.len());
        for command in program {
            if let ResolvedNCommand::Input { span, name, file } = &command {
                lowered.extend(
                    Self::input_actions(egraph, span, name, file)?
                        .into_iter()
                        .map(ResolvedNCommand::CoreAction),
                );
            } else {
                lowered.push(command);
            }
        }
        Ok(lowered)
    }

    /// Mint a `Rule` or `Fiat` proof of the equality `a = b`, both values of
    /// `sort`. Only `Fiat` names the two endpoints; a rule proof's proposition
    /// comes from its column. Panics on merge justifications (merge bodies
    /// contain no `union` actions).
    fn edge_proof(&mut self, emit: &mut Emit, sort: &str, a: &str, b: &str) -> String {
        match emit.justification {
            Justification::Rule(..) => self.rule_row(emit),
            Justification::Fiat => {
                let fiat = self.fiat_constructor(sort);
                self.mint(emit.stmts, &fiat, &format!("{a} {b}"))
            }
            Justification::MergeIdx(..) | Justification::MergeRow(..) => panic!(
                "Merge functions do not include union actions, so proof should not be by merge"
            ),
        }
    }

    /// Mint the rule proof row the emit's justification names. Proof conversion
    /// derives the proposition from the column alone, so the row stores no terms.
    ///
    /// A head's first row carries the body premises inline; every row after the
    /// head has interned a subterm chains onto the row before that interning,
    /// adding its bridge. So a row names exactly the bridges the head had
    /// recorded when it minted the row.
    fn rule_row(&mut self, emit: &mut Emit) -> String {
        let justification = emit.justification;
        let proof = match emit.head.link() {
            None => self.inline_rule_row(emit.stmts, justification),
            Some((prev, bridge)) => self.link_rule_row(emit.stmts, justification, &prev, &bridge),
        };
        emit.head.minted(&proof);
        proof
    }

    /// A rule proof row carrying the head's body premises as columns.
    fn inline_rule_row(
        &mut self,
        stmts: &mut Vec<String>,
        justification: &Justification,
    ) -> String {
        let Justification::Rule(rule_name, premises, _) = justification else {
            panic!("only a rule justification mints a rule proof row");
        };
        let (rule_name, premises) = (rule_name.clone(), premises.clone());
        let column = justification.column_expr();
        let rule = self.proof_names().fused_rule(premises.len());
        let premises = premises.iter().map(|p| format!("{p} ")).collect::<String>();
        self.mint(stmts, &rule, &format!("{rule_name} {premises}{column}"))
    }

    /// A rule proof row naming `prev` — a row of the same head, carrying the body
    /// premises and every earlier bridge — plus `bridge`.
    fn link_rule_row(
        &mut self,
        stmts: &mut Vec<String>,
        justification: &Justification,
        prev: &str,
        bridge: &str,
    ) -> String {
        assert!(
            matches!(justification, Justification::Rule(..)),
            "only a rule justification mints a rule proof row"
        );
        let column = justification.column_expr();
        let link = self.proof_names().rule_link_constructor.clone();
        self.mint(stmts, &link, &format!("{prev} {bridge} {column}"))
    }

    /// A built term's connector proof as a proof node, minting the rule proof row
    /// for a [`Connector::Column`].
    fn connector_node(&mut self, emit: &mut Emit, connector: &Connector) -> String {
        match connector {
            Connector::Node(node) => node.clone(),
            Connector::Column(column) => {
                let connector = emit
                    .justification
                    .at(HeadColumn::Numbered(column.to_string()));
                self.rule_row(&mut emit.justified_by(&connector))
            }
        }
    }

    /// Mark two things as equal, adding proof if proofs are enabled. Claims the
    /// head's [`HeadPosition::Union`] columns, writes any proof-relation mints,
    /// and returns the `(set @UF ...)` action, which the caller must emit after
    /// them.
    fn union(&mut self, emit: &mut Emit, type_name: &str, lhs: &Operand, rhs: &Operand) -> String {
        let run = emit.head.claim(HeadPosition::Union);
        let uf_name = self.uf_name(type_name);
        let (larger, smaller) = ordered_endpoints(lhs, rhs);
        // `@UF : (S) -> (S, {Unit|Proof})` is keyed by the larger endpoint; its
        // `:merge` resolves conflicting parents. The second column carries a proof
        // `larger = smaller` (`()` in term mode).
        let proof = if !self.egraph.proof_state.proofs_enabled {
            "()".to_string()
        } else if emit.head.composes() {
            self.composed_union_edge(emit, type_name, lhs, rhs)
        } else {
            self.skeleton_union_edge(emit, lhs, rhs, run)
        };
        format!("(set ({uf_name} {larger}) (values {smaller} {proof}))")
    }

    /// The `larger = smaller` proof a `union` in a rule head stores in `@UF`. The
    /// column and the operands' bridge premises determine the whole composition,
    /// so one row records it.
    fn skeleton_union_edge(
        &mut self,
        emit: &mut Emit,
        lhs: &Operand,
        rhs: &Operand,
        run: Option<HeadRun>,
    ) -> String {
        let run = run.expect("a rule head's unions are numbered");
        // `proof-of-max` picks the direction the `larger = smaller` edge needs,
        // by the same value ordering as `ordering-max`, over the two columns'
        // `i64` literals.
        let oriented = format!(
            "(proof-of-max {} {} {} {})",
            lhs.value,
            run.column(HeadProof::EdgeFromLhs),
            rhs.value,
            run.column(HeadProof::EdgeFromRhs)
        );
        let oriented = emit.justification.at(HeadColumn::Numbered(oriented));
        self.rule_row(&mut emit.justified_by(&oriented))
    }

    /// The `larger = smaller` proof a `union` outside a rule head stores in `@UF`,
    /// composed here rather than recorded: nothing downstream rebuilds it.
    fn composed_union_edge(
        &mut self,
        emit: &mut Emit,
        type_name: &str,
        lhs: &Operand,
        rhs: &Operand,
    ) -> String {
        // No column names any of these rows, so each states its own conclusion.
        let fiat = Justification::Fiat;
        let emit = &mut emit.justified_by(&fiat);

        // Neither operand was a canonicalized constructor term (no connector), so
        // both e-classes' terms are stable: build the edge proof directly over them.
        if lhs.connector.is_none() && rhs.connector.is_none() {
            let (larger, smaller) = ordered_endpoints(lhs, rhs);
            return self.edge_proof(emit, type_name, &larger, &smaller);
        }

        // A canonicalized operand's deduped e-class may already be unioned with a
        // differently-shaped term, so its term floats. Build the base equality over
        // the *natural* forms (pinned to the enode the rule built), then route
        // each deduped e-class to a shared natural form and orient the edge to
        // `larger = smaller` with proof-of-max/min.
        //
        // Built over the operands in source order, so it states the conclusion
        // forwards.
        let base_proof = self.edge_proof(emit, type_name, &lhs.natural, &rhs.natural);

        // The shared natural form is the canonicalized side's natural (pinned to
        // the enode the rule built), so the Trans goes through it rather than
        // through the deduped e-class.
        let lhs_conn = lhs.connector.as_ref().map(|c| self.connector_node(emit, c));
        let rhs_conn = rhs.connector.as_ref().map(|c| self.connector_node(emit, c));
        let (lhs_to_shared, rhs_to_shared) = self.union_to_shared(base_proof, lhs_conn, rhs_conn);
        // `proof-of-max`/`min` read the two sides directly rather than through a
        // mint, so bind them here.
        self.emit_pending_group(emit.stmts, &lhs_to_shared);
        self.emit_pending_group(emit.stmts, &rhs_to_shared);
        let (lhs, rhs) = (&lhs.value, &rhs.value);
        let max_pf = self.fresh_var();
        emit.stmts.push(format!(
            "(let {max_pf} (proof-of-max {lhs} {lhs_to_shared} {rhs} {rhs_to_shared}))"
        ));
        let min_pf = self.fresh_var();
        emit.stmts.push(format!(
            "(let {min_pf} (proof-of-min {lhs} {lhs_to_shared} {rhs} {rhs_to_shared}))"
        ));
        let sym_min = self.mint_sym(&min_pf);
        let edge = self.mint_trans(&max_pf, &sym_min);
        // The `@UF` row below is the caller's, not a mint of ours.
        self.emit_pending_group(emit.stmts, &edge);
        edge
    }

    /// Lower a construct-into guest `(let guest (F args))`: point its view value
    /// at `target`'s e-class with a plain `set` (a collision with an existing
    /// `F(args)` unions the two via the view's `:merge`). In proof mode the view
    /// row also carries the proof `target = F(args)`, the dropped union's edge.
    ///
    /// Returns the guest's term, which the caller binds like any other `let`.
    fn instrument_construct_into(
        &mut self,
        emit: &mut Emit,
        expr: &ResolvedExpr,
        target: &Operand,
        scope: &Scope,
    ) -> Operand {
        let (func_type, args) = constructor_operand(expr)
            .expect("construct-into guest must be a constructor application");
        let ctor_name = func_type.name.clone();
        let child_vals: Vec<Operand> = args
            .iter()
            .map(|arg| self.instrument_action_expr(arg, emit, scope))
            .collect();
        let run = emit.head.claim(HeadPosition::Guest);
        let target_id = &target.value;

        if !self.proofs_enabled() {
            let child_ids = ids(&child_vals);
            emit.stmts.push(format!(
                "(set ({ctor_name} {} {target_id}) ())",
                ListDisplay(&child_ids, " ")
            ));
            let update = self.update_fd_view(&ctor_name, &child_ids, target_id, "()");
            emit.stmts.push(update);
            return Operand::plain(target_id.clone());
        }

        let sort_name = func_type.output().name().to_string();
        let view = self.view_name(&ctor_name);
        let own = emit.justification.at(head_column(run, HeadProof::Own));
        let Natural {
            dedup_args,
            fv_nat,
            to_dedup: nat_to_dedup,
        } = self.build_natural_with_congr(&mut emit.justified_by(&own), &ctor_name, &child_vals);
        let view_proof = match &nat_to_dedup {
            Some(chain) => {
                let edge = self.edge_proof(emit, &sort_name, &target.natural, &fv_nat);
                let target_conn = target
                    .connector
                    .as_ref()
                    .map(|conn| self.connector_node(emit, conn));
                self.guest_view(edge, chain.clone(), target_conn)
            }
            // The guest's columns plus its bridge premises determine the whole
            // composition, so one row records it and the edge proof it is built
            // from needs no row of its own.
            None => {
                let view = emit
                    .justification
                    .at(head_column(run, HeadProof::GuestView));
                self.rule_row(&mut emit.justified_by(&view))
            }
        };
        // The guest's term keeps its own id (`fv_nat`); only the view VALUE uses
        // the target. Emitting `(F dedup_args target)` would add the guest's
        // shape to `target`'s term relation, making the term proof reconstruction
        // picks for `target` ambiguous (it reads term rows, not views).
        let dedup_disp = ListDisplay(&dedup_args, " ").to_string();
        // The view row below carries the proof directly, not through a mint.
        self.emit_pending_group(emit.stmts, &view_proof);
        emit.stmts.push(format!(
            "(set ({view} {dedup_disp}) (values {target_id} {view_proof}))"
        ));
        let guest_conn = match &nat_to_dedup {
            Some(chain) => Connector::Node(self.level_connector(chain, &view_proof)),
            None => Connector::Column(
                run.expect("a rule head's guest is numbered")
                    .column(HeadProof::Connector),
            ),
        };
        Operand::built(target_id.clone(), fv_nat, guest_conn)
    }

    /// The parent table is the database representation of a union-find datastructure.
    /// When one term has two parents, those parents are unioned in the merge action.
    /// Also, we have a rule that maintains the invariant that each term points to its
    /// canonical representative.
    fn declare_sort(&mut self, sort_name: &str, is_container: bool) -> Vec<Command> {
        // Containers are canonicalized structurally, not unioned directly, so
        // they get no union-find.
        if is_container {
            return vec![];
        }
        self.declare_sort_eq(sort_name)
    }

    /// The shared `:merge` block for a collision that unions two members of one
    /// e-class: keep `(ordering-min old0 new0)` with the smaller side's carried
    /// proof, and `set` the displaced larger side's `@UF` edge to the smaller
    /// with a proof of `larger = smaller`. That proof is one packed row naming
    /// both carried proofs, standing for `composition` over them — the larger
    /// side's is column 0 and the smaller side's column 1.
    ///
    /// Returns the packed constructor's declaration, which the caller must emit
    /// ahead of the block, and the block itself.
    fn ordered_union_merge(&mut self, uf_name: &str, composition: Skeleton) -> (String, String) {
        if !self.proofs_enabled() {
            return (
                String::new(),
                format!(
                    "((set ({uf_name} (ordering-max old0 new0)) (values (ordering-min old0 new0) ()))
                  (values (ordering-min old0 new0) ()))"
                ),
            );
        }
        let (displaced, decl) = self.packed_proof_constructor(composition.width());
        let spelling = composition.spelling();
        let mut mints = vec![];
        let row = format!("\"{spelling}\" hi_pf_ lo_pf_");
        let displaced_pf = self.mint(&mut mints, &displaced, &row);
        let mints_str = mints.join("\n                  ");
        let merge = format!(
            "((let hi_pf_ (proof-of-max old0 old1 new0 new1))
              (let lo_pf_ (proof-of-min old0 old1 new0 new1))
              {mints_str}
              (set ({uf_name} (ordering-max old0 new0))
                   (values (ordering-min old0 new0) {displaced_pf}))
              (values (ordering-min old0 new0) lo_pf_))"
        );
        (decl, merge)
    }

    /// Declare a sort's union-find `@UF : (S) -> (S, {Unit|Proof})`, mapping each
    /// term to its parent plus a proof `key = parent` (`()` in term mode). Its
    /// `:merge` resolves conflicting parents (see `proof_encoding.md`). Also emits
    /// the `path_compress` rule.
    fn declare_sort_eq(&mut self, sort_name: &str) -> Vec<Command> {
        let proofs = self.proofs_enabled();
        let uf_name = self.uf_name(sort_name);
        let proof_type = self.proof_type_str().to_string();
        let fresh_name = self.egraph.parser.symbol_gen.fresh("uf_path_compress");
        let path_compress_ruleset_name = self.proof_names().path_compress_ruleset_name.clone();

        let a = self.egraph.parser.symbol_gen.fresh("uf_a");
        let b = self.egraph.parser.symbol_gen.fresh("uf_b");
        let c = self.egraph.parser.symbol_gen.fresh("uf_c");
        let pb = self.egraph.parser.symbol_gen.fresh("uf_pb");
        let pc = self.egraph.parser.symbol_gen.fresh("uf_pc");

        // An `@UF` row's carried proof proves `key = parent`, so both share their
        // lhs and it is the larger side's that the composition reverses.
        let (packed_decl, uf_merge) =
            self.ordered_union_merge(&uf_name, Skeleton::Leaf(0).sym().trans(Skeleton::Leaf(1)));
        // path compression: a->b (pb: a=b), b->c (pc: b=c)  =>  a->c (Trans pb pc: a=c)
        let (compressed_proof_lets, compressed_proof) = if proofs {
            let trans = self.proof_names().eq_trans_constructor.clone();
            let mut mints = vec![];
            let pf = self.mint(&mut mints, &trans, &format!("{pb} {pc}"));
            (mints.join("\n                    "), pf)
        } else {
            (String::new(), "()".to_string())
        };

        let code = format!(
            "{packed_decl}
             (function {uf_name} ({sort_name}) ({sort_name} {proof_type}) :merge {uf_merge} :unextractable :internal-hidden :internal-identity-vals 1)
             (rule ((= (values {b} {pb}) ({uf_name} {a}))
                    (= (values {c} {pc}) ({uf_name} {b}))
                    (!= {b} {c}))
                  ({compressed_proof_lets}
                   (set ({uf_name} {a}) (values {c} {compressed_proof})))
                   :ruleset {path_compress_ruleset_name}
                   :name \"{fresh_name}\")
                   "
        );

        self.parse_program(&code)
    }

    /// A global is a `:internal-let` function; in the encoding it is treated like a
    /// nullary constructor (FD view, congruence merge, readable value+proof) rather
    /// than a `:no-merge` custom function.
    pub(super) fn is_encoded_global(&self, fdecl: &ResolvedFunctionDecl) -> bool {
        fdecl.internal_let
    }

    /// Whether the function's output value *is* its e-class, so the term relation
    /// needs no separate output column and the view is the congruence FD
    /// `(children) -> (eclass, proof)`. Holds for constructors and encoded globals.
    pub(super) fn output_is_eclass(&self, fdecl: &ResolvedFunctionDecl) -> bool {
        fdecl.subtype == FunctionSubtype::Constructor || self.is_encoded_global(fdecl)
    }

    /// The `:merge` expression for a custom function's FD pair-valued view
    /// `(children) -> (values output proof)`. On a children-key collision it runs
    /// the user's merge body once (unlike a constructor's congruence, it performs
    /// no `@UF` union): `old`/`new` bind to the two colliding output columns
    /// (`old0`/`new0`) and the carried view proofs to `old1`/`new1`. The result is
    /// `(values merged rowproof)`, where `merged` is the (canonically-minted) merge
    /// body and `rowproof` is a children-free `MergeRow` (`()` in term mode).
    ///
    /// Running the merge inside the view's `:merge` computes the body exactly
    /// once; computing it twice mints extra, over-merged term rows.
    fn custom_view_merge(&mut self, fdecl: &ResolvedFunctionDecl) -> String {
        let name = fdecl.name.clone();
        let merge = fdecl
            .merge
            .as_ref()
            .expect("custom FD view requires a :merge");

        let mut body_code = vec![];
        let mut idx = 0usize;
        // A merge body concludes nothing a rule proof row can be named by, so
        // its proofs are composed here.
        let mut head = Head::composed();
        // The row the whole body computes; each subexpression states its own
        // `MergeIdx` instead.
        let row = Justification::MergeRow(name.clone(), "old1".to_string(), "new1".to_string());
        let mut emit = Emit {
            stmts: &mut body_code,
            head: &mut head,
            justification: &row,
        };
        let merged = self
            .instrument_merge_body(&mut emit, &merge.result, &name, &mut idx)
            .value;
        // The merge body's outermost term records a connector nothing composes
        // with; whatever is still deferred reached no statement.
        self.drop_pending_lookups();
        let row_proof = if self.egraph.proof_state.proofs_enabled {
            let fresh = self.reflexive_for_justification(&mut emit, "", "");
            // Keep the proof column stable: when the merged output equals a
            // colliding premise's output (as with idempotent `min`/`max`/... merges
            // that keep one input), reuse that premise's existing proof so the row
            // stays value-identical and the merge saturates. Otherwise the fresh
            // `MergeRow` justifies the newly-computed output.
            format!("(select-eq {merged} old0 old1 (select-eq {merged} new0 new1 {fresh}))")
        } else {
            "()".to_string()
        };
        let value = format!("(values {merged} {row_proof})");
        if body_code.is_empty() {
            value
        } else {
            format!("({}\n{value})", body_code.join("\n"))
        }
    }

    /// Each function/constructor gets a term table and a view table.
    /// The term table stores underlying representative terms.
    /// The view table stores child terms and their eclass.
    /// The view table is mutated using delete, but we never delete from term tables.
    /// We re-use the original name of the function for the term table.
    fn term_and_view(&mut self, fdecl: &ResolvedFunctionDecl) -> Vec<Command> {
        let schema = &fdecl.schema;
        let out_type = schema.output().clone();

        let name = &fdecl.name;
        let view_name = self.view_name(&fdecl.name);
        let in_sorts = ListDisplay(schema.input.clone(), " ");
        let fresh_sort = self.egraph.parser.symbol_gen.fresh("view");
        let index_decls = self.declare_view_indexes(fdecl);
        // Constructors and encoded globals give the term row `(children eclass)`;
        // a Custom function returning a distinct value (e.g. `-> i64`) keeps an
        // output column plus a fresh eclass column.
        let output_is_eclass = self.output_is_eclass(fdecl);
        let term_sorts = format!(
            "{in_sorts} {}",
            if output_is_eclass {
                "".to_string()
            } else {
                schema.output().to_string()
            }
        );

        let view_sort = if output_is_eclass {
            schema.output().clone()
        } else {
            fresh_sort.clone()
        };
        // Record the term's eclass sort (its `view_sort`) so a global lookup's
        // fallback id is minted at the right sort.
        self.egraph
            .proof_state
            .proof_names
            .fn_to_term_sort
            .insert(name.clone(), view_sort.clone());
        let proof_type = self.proof_type_str().to_string();
        let mut view_flags = String::new();
        if fdecl.unextractable {
            view_flags.push_str(" :unextractable");
        }
        if fdecl.internal_hidden {
            view_flags.push_str(" :internal-hidden");
        }
        if fdecl.internal_let {
            view_flags.push_str(" :internal-let");
        }
        // The view carries the user operation's extraction cost (the term table
        // is a relation and can't carry `:cost`); the extractor reads it here.
        if let Some(cost) = fdecl.cost {
            view_flags.push_str(&format!(" :internal-cost {cost}"));
        }
        // Every encoded function uses the FD pair-valued view `(children) ->
        // (output, {Unit|Proof})` keyed on children only; the branches below
        // differ in how the `:merge` resolves a children-key collision.
        let mut packed_decl = String::new();
        let view_decl = if output_is_eclass {
            // Two rows conflicting on the same children are congruent: keep the
            // smaller eclass and union the two eclasses in the sort's `@UF`.
            let uf_name = self.uf_name(schema.output());
            // A view's carried proof proves `eclass = f(children)`, so both share
            // their rhs and it is the smaller side's that the composition
            // reverses.
            let (decl, congruence_merge) = self
                .ordered_union_merge(&uf_name, Skeleton::Leaf(0).trans(Skeleton::Leaf(1).sym()));
            packed_decl = decl;
            format!(
                "(function {view_name} ({in_sorts}) ({out_type} {proof_type}) :merge {congruence_merge} :internal-term-constructor {name}{view_flags} :internal-identity-vals 1)"
            )
        } else if fdecl.merge.is_some() {
            // Custom function with a `:merge`: the view `:merge` runs the user
            // merge once (see `custom_view_merge`). No `@UF` union.
            let custom_merge = self.custom_view_merge(fdecl);
            format!(
                "(function {view_name} ({in_sorts}) ({out_type} {proof_type}) :merge {custom_merge} :internal-term-constructor {name}{view_flags} :internal-identity-vals 1)"
            )
        } else {
            // Primitive/`Unit`-output `:no-merge` custom: the view is declared native
            // `:no-merge` with `:internal-identity-vals 1` — a children collision
            // keeps the old row when value column 0 (the output) is unchanged (raw
            // equality is equality for a primitive output) and panics when it
            // differs. The proof column (value column 1) is a payload the identity
            // guard ignores.
            debug_assert!(
                !fdecl.resolved_schema.output().is_eq_sort(),
                "eq-sort `:no-merge` must be rejected by command_supports_proof_encoding"
            );
            format!(
                "(function {view_name} ({in_sorts}) ({out_type} {proof_type}) :no-merge :internal-term-constructor {name}{view_flags} :internal-identity-vals 1)"
            )
        };
        // `fresh_sort` is the term's e-class sort only for a custom function whose
        // output is a distinct value (see `view_sort` above); a constructor/global
        // reuses its output sort, leaving `fresh_sort` unused.
        let fresh_sort_decl = if output_is_eclass {
            String::new()
        } else {
            format!("(sort {fresh_sort})")
        };
        // The term relation is a term node (`:internal-term-node`): its rows are
        // reconstructed by proof extraction, with the minted id as the last input.
        self.parse_program(&format!(
            "
            {fresh_sort_decl}
            (function {name} ({term_sorts} {view_sort}) Unit :no-merge :internal-hidden :internal-term-node)
            {packed_decl}{view_decl}
            {index_decls}",
        ))
    }

    // Actions need to be instrumented to add to the view
    // as well as to the terms tables.
    //
    // Every proof minted here is named by the column the walk is at, so an
    // action's operands are instrumented before the columns the action itself
    // claims (see [`crate::proofs::proof_head`]).
    fn instrument_action(&mut self, action: &ResolvedAction, emit: &mut Emit, scope: &mut Scope) {
        match action {
            ResolvedAction::Let(_span, v, generic_expr) => {
                let bound = self.instrument_action_expr(generic_expr, emit, scope);
                emit.stmts.push(format!("(let {} {})", v.name, bound.value));
                scope.bind(&v.name, &bound);
            }
            ResolvedAction::Set(_span, h, generic_exprs, generic_expr) => {
                let ResolvedCall::Func(func_type) = h else {
                    panic!(
                        "Set action on non-function, should have been prevented by typechecking"
                    );
                };

                let mut exprs = vec![];
                for e in generic_exprs.iter().chain(std::iter::once(generic_expr)) {
                    exprs.push(self.instrument_action_expr(e, emit, scope));
                }
                // The row `(f args… value)` is the `set`'s own conclusion, and its
                // only column. Building a constructor claims two more, so a `set`
                // on one would misnumber every later column rather than fail.
                assert_ne!(
                    func_type.subtype,
                    FunctionSubtype::Constructor,
                    "`set` on a constructor should have been rejected by typechecking"
                );
                let run = emit.head.claim(HeadPosition::Set);

                // Global definition `(set (x) e)`: x is a nullary `:internal-let`
                // function aliasing e. Store e's value+proof directly in x's FD view
                // (x's e-class *is* e's) — no term mint, which would use the wrong
                // arity for x's term relation (its output is the eclass, so it has
                // no separate output column).
                if generic_exprs.is_empty() && self.egraph.type_info.is_global(&func_type.name) {
                    let e_value = exprs.pop().expect("a set has a value");
                    let proof = if self.proofs_enabled() {
                        self.global_value_proof(emit, func_type, &e_value)
                    } else {
                        "()".to_string()
                    };
                    // Term row (`x`'s e-class is e's) + the FD view `() -> (val, proof)`.
                    let e_value = e_value.value;
                    emit.stmts
                        .push(format!("(set ({} {e_value}) ())", func_type.name));
                    let update = self.update_fd_view(&func_type.name, &[], &e_value, &proof);
                    emit.stmts.push(update);
                    return;
                }

                let own = emit.justification.at(head_column(run, HeadProof::Own));
                self.add_term_and_view(&mut emit.justified_by(&own), func_type, &exprs, run);
            }
            ResolvedAction::Change(_span, change, h, generic_exprs) => {
                if let ResolvedCall::Func(func_type) = h {
                    // `change` concludes nothing, so its arguments hold no column
                    // for conversion to read back: they compose like a top-level
                    // action, and the head's numbering resumes after them.
                    let children = emit.composing(|emit| {
                        generic_exprs
                            .iter()
                            .map(|e| self.instrument_action_expr(e, emit, scope))
                            .collect::<Vec<_>>()
                    });
                    let args = ListDisplay(ids(&children), " ").to_string();

                    match change {
                        // Removing the view row here is the uninstrumented meaning
                        // of `delete`: execution stages the removal to the batch
                        // commit, which applies removals ahead of insertions. The
                        // term relation keeps its row so proofs can still name the
                        // deleted term.
                        Change::Delete => {
                            let view = self.view_name(&func_type.name);
                            emit.stmts.push(format!("(delete ({view} {args}))"));
                        }
                        Change::Subsume => {
                            let symbol = self.subsume_marker(&func_type.name, &func_type.input);
                            emit.stmts.push(format!("(set ({symbol} {args}) ())"));
                        }
                    }
                } else {
                    panic!(
                        "Delete action on non-function, should have been prevented by typechecking"
                    );
                }
            }
            ResolvedAction::Union(_span, generic_expr, generic_expr1) => {
                // A union whose operand is a freshly-built constructor term is
                // optimized upstream in `instrument_actions`; this arm handles
                // the remaining general unions.
                let v1 = self.instrument_action_expr(generic_expr, emit, scope);
                let v2 = self.instrument_action_expr(generic_expr1, emit, scope);
                let ot = generic_expr.output_type();
                let type_name = ot.name();
                let unioned = self.union(emit, type_name, &v1, &v2);
                emit.stmts.push(unioned);
            }
            ResolvedAction::Panic(..) => {
                emit.stmts.push(format!("{action}"));
            }
            ResolvedAction::Expr(_span, generic_expr) => {
                self.instrument_action_expr(generic_expr, emit, scope);
            }
        }
    }

    /// A proof of `fv = fv` under the emit's justification.
    ///
    /// The caller must be at a position whose own conclusion is reflexive: a rule
    /// justification's proof states whatever its column says and is marked
    /// reflexive regardless, so calling this at an equality — a `union`'s — would
    /// have the compositions built on it silently drop a real proof.
    fn reflexive_for_justification(&mut self, emit: &mut Emit, fv: &str, sort: &str) -> String {
        match emit.justification {
            // The head's own conclusion here is `fv = fv` (`fv`/`sort` unused:
            // the proposition comes from the column).
            Justification::Rule(..) => {
                let proof = self.rule_row(emit);
                self.mark_reflexive(&proof);
                proof
            }
            Justification::Fiat => self.fiat_reflexive_proof(emit.stmts, fv, sort),
            // Term-free: no endpoint named (`fv`/`sort` unused). The checker
            // reconstructs the conclusion from the merge body + premise outputs.
            Justification::MergeIdx(fn_name, p1, p2, idx) => {
                let merge_idx = self.proof_names().merge_fn_idx_constructor.clone();
                let row = format!("\"{fn_name}\" {p1} {p2} {idx}");
                self.mint(emit.stmts, &merge_idx, &row)
            }
            Justification::MergeRow(fn_name, p1, p2) => {
                let merge_row = self.proof_names().merge_fn_row_constructor.clone();
                let row = format!("\"{fn_name}\" {p1} {p2}");
                self.mint(emit.stmts, &merge_row, &row)
            }
        }
    }

    /// A `Fiat` proof of `fv = fv`, appending its mint to `stmts`. `fv` is a
    /// value of `sort`, which fixes the fiat relation naming it.
    pub(super) fn fiat_reflexive_proof(
        &mut self,
        stmts: &mut Vec<String>,
        fv: &str,
        sort: &str,
    ) -> String {
        let fiat = self.fiat_constructor(sort);
        let proof = self.mint(stmts, &fiat, &format!("{fv} {fv}"));
        self.mark_reflexive(&proof);
        proof
    }

    /// Proof stored in a global's FD view for the value `e` it aliases.
    ///
    /// When `e` is a built term (e.g. `(Plus …)`), the encoding has already proved
    /// its *natural* form — the literal term the checker reconstructs from the
    /// global's `(let x e)` — and holds a `connector : natural = e`. Anchor the
    /// global's proof on that natural form (a reflexive `e = e` routed through it)
    /// instead of fiat-ing the canonical value directly: the value's shape may be a
    /// rewritten (canonicalized) child the checker cannot establish, whereas the
    /// natural form is exactly the global definition it can. An atomic value (a
    /// literal, or a bare reference to another global) has no connector and is
    /// fiat-ed directly — a literal is self-justifying and a global alias is
    /// already established.
    ///
    /// A global is only ever set by a top-level action — a rule head that names
    /// one reads it as a query variable — so the connector here is always a proof
    /// node the encoder minted, never a rule head's column.
    fn global_value_proof(
        &mut self,
        emit: &mut Emit,
        func_type: &FuncType,
        e_value: &Operand,
    ) -> String {
        let value = &e_value.value;
        match &e_value.connector {
            Some(Connector::Node(connector)) => {
                let connector = connector.clone();
                let sym = self.proof_names().eq_sym_constructor.clone();
                let trans = self.proof_names().eq_trans_constructor.clone();
                let sym_conn = self.mint(emit.stmts, &sym, &connector);
                let row = format!("{sym_conn} {connector}");
                self.mint(emit.stmts, &trans, &row)
            }
            Some(Connector::Column(column)) => {
                panic!("a global's value cannot be named by rule head column {column}")
            }
            None => {
                let sort = self.term_sort(&func_type.name);
                self.reflexive_for_justification(emit, value, &sort)
            }
        }
    }

    /// Write a row into a functional-dependency view
    /// `(set (@FView children) (values eclass proof))`. Re-setting an existing `children` key with a
    /// different `eclass` triggers the view's `:merge`.
    pub(super) fn update_fd_view(
        &mut self,
        fname: &str,
        children: &[String],
        value: &str,
        proof: &str,
    ) -> String {
        let view_name = self.view_name(fname);
        format!(
            "(set ({view_name} {}) (values {value} {proof}))",
            ListDisplay(children, " ")
        )
    }

    /// Record that `proof` proves `t = t`, which the `mint_*` constructors use
    /// to drop the steps composed onto it.
    pub(crate) fn mark_reflexive(&mut self, proof: &str) {
        self.reflexive.insert(proof.to_string());
    }

    /// Whether `proof` is known to prove `t = t`.
    fn is_reflexive(&self, proof: &str) -> bool {
        self.reflexive.contains(proof)
    }

    /// `Sym(proof)`, or `proof` itself when it is reflexive.
    ///
    /// Held back, like the other two composites: the row is written where
    /// something reads the name, so a composition nothing reads is never written
    /// and one that is becomes a single row (see [`Self::emit_composition`]).
    pub(crate) fn mint_sym(&mut self, proof: &str) -> String {
        if self.is_reflexive(proof) {
            return proof.to_string();
        }
        let inner = self.composition(proof);
        self.compose(inner.sym())
    }

    /// `Trans(lhs, rhs)`, dropping whichever side is reflexive. Held back, see
    /// [`Self::mint_sym`].
    pub(crate) fn mint_trans(&mut self, lhs: &str, rhs: &str) -> String {
        if self.is_reflexive(lhs) {
            return rhs.to_string();
        }
        if self.is_reflexive(rhs) {
            return lhs.to_string();
        }
        let (lhs, rhs) = (self.composition(lhs), self.composition(rhs));
        self.compose(lhs.trans(rhs))
    }

    /// `Congr(acc, idx, step)`, or `acc` when `step` is reflexive. Held back, see
    /// [`Self::mint_sym`].
    pub(crate) fn mint_congr(&mut self, acc: &str, idx: usize, step: &str) -> String {
        if self.is_reflexive(step) {
            return acc.to_string();
        }
        let (acc, step) = (self.composition(acc), self.composition(step));
        self.compose(acc.congr(idx, step))
    }

    /// `Proj(base, child)`, the reflexive proof of `base`'s right-hand side's
    /// child at `child`. Held back, see [`Self::mint_sym`].
    pub(crate) fn mint_proj(&mut self, base: &str, child: usize) -> String {
        let base = self.composition(base);
        let proof = self.compose(base.proj(child));
        self.mark_reflexive(&proof);
        proof
    }

    /// The proof of `t = t` for `base`'s left-hand side `t`, given
    /// `base : t = <term>`. Held back, see [`Self::mint_sym`].
    pub(crate) fn mint_lhs_reflexive(&mut self, base: &str) -> String {
        let back = self.mint_sym(base);
        let proof = self.mint_trans(base, &back);
        self.mark_reflexive(&proof);
        proof
    }

    /// Record that the row proof `row_proof` reaches `value` (see [`Anchor`]).
    pub(crate) fn offer_anchor(&mut self, value: &str, row_proof: &str, anchor: Anchor) {
        if self.proofs_enabled() {
            self.anchors.offer(value, row_proof, anchor);
        }
    }

    /// Record that the body only matches when `left` and `right` are equal.
    pub(crate) fn alias_anchor(&mut self, left: &str, right: &str) {
        if self.proofs_enabled() {
            self.anchors.alias(left, right);
        }
    }

    /// A fresh proof variable standing for `value`'s reflexive anchor, bound
    /// once [`Self::bind_anchors`] has seen the whole body. Reflexive from here
    /// on, so a composition reading it drops it as a step.
    pub(crate) fn request_anchor(&mut self, value: &str) -> String {
        let proof = self.fresh_var();
        self.anchors.request(&proof, value);
        self.mark_reflexive(&proof);
        proof
    }

    /// [`Self::request_anchor`] for a value a body primitive read out of a
    /// container: nothing in the query names it as a term, but it is a child of
    /// the container it came out of, and the body anchors that.
    ///
    /// `rule_name` and `body_index` locate the reading call in its rule's body so
    /// proof conversion can recover the resolved primitive and run its validator
    /// on the argument terms. Outside a rule body there is no such locator, and
    /// the anchor is left unsupplied — every such context drops its anchors
    /// unread.
    pub(crate) fn request_element_anchor(
        &mut self,
        value: &str,
        rule_name: Option<&str>,
        body_index: usize,
        container_index: usize,
        containers: Vec<String>,
        arg_proofs: Vec<Option<String>>,
    ) -> String {
        if let Some(rule_name) = rule_name {
            self.anchors.offer_element(Element {
                containers,
                value: value.to_string(),
                rule_name: rule_name.to_string(),
                body_index,
                arg_proofs,
                container_index,
            });
        }
        self.request_anchor(value)
    }

    /// Bind every anchor the body asked for, and clear the body's anchors for
    /// the next one. Each is deferred, so it lands where it is first read and
    /// nowhere if nothing reads it.
    ///
    /// An anchor no body atom reaches is left unbound. Proof support rejects such
    /// a rule before it is encoded, which is the complete gate: a composition over
    /// an unbound anchor drops it rather than reading it (soundly — its conclusion
    /// is `t = t`), so [`Self::emit_pending_group`]'s assert only catches a
    /// statement that names the variable directly.
    pub(crate) fn bind_anchors(&mut self) {
        let anchors = std::mem::take(&mut self.anchors);
        for (proof, value) in &anchors.requests {
            let Some((row_proof, anchor, chain)) = anchors.anchor_chain(value) else {
                self.unanchored.insert(proof.clone(), value.clone());
                continue;
            };
            let derived = self.anchor_composition(&row_proof, anchor);
            if chain.is_empty() {
                // `derived` is itself deferred: alias `proof` onto whatever it
                // holds so the row lands where the anchor is first read.
                let held = self
                    .deferred
                    .remove(&derived)
                    .expect("a minted composition is held back");
                self.deferred.insert(proof.clone(), held);
                continue;
            }
            // The row the projections stand on gets a row inside this group
            // rather than being shared, so the group stays self-contained.
            let mut group = vec![];
            self.emit_pending_group(&mut group, &derived);
            let mut base = derived;
            let mut reads = vec![];
            for (depth, element) in chain.iter().enumerate() {
                let arity = element.arg_proofs.len();
                let proj_prim = self.proj_prim_constructor(arity);
                let mint = crate::proofs::proof_fresh::mint_prim_name(&proj_prim);
                let projected = if depth + 1 == chain.len() {
                    proof.clone()
                } else {
                    self.fresh_var()
                };
                // The container's argument is the projection's base; the rest are
                // whatever the body walk proved for them, and are emitted ahead of
                // this group wherever it lands.
                let args: Vec<String> = element
                    .arg_proofs
                    .iter()
                    .enumerate()
                    .map(|(i, arg)| match arg {
                        _ if i == element.container_index => base.clone(),
                        Some(arg) => {
                            reads.push(arg.clone());
                            arg.clone()
                        }
                        None => panic!(
                            "argument {i} of the body call reading `{}` has no proof",
                            element.value
                        ),
                    })
                    .collect();
                let (rule, index) = (&element.rule_name, element.body_index);
                let args = ListDisplay(&args, " ");
                group.push(format!("(let {projected} ({mint} {rule} {index} {args}))"));
                base = projected;
            }
            self.defer_lookup_reading(proof, group, reads);
        }
    }

    /// The composition reaching a term from the row proof that mentions it.
    fn anchor_composition(&mut self, row_proof: &str, anchor: Anchor) -> String {
        match anchor {
            Anchor::Child(child) => self.mint_proj(row_proof, child),
            Anchor::Lhs => self.mint_lhs_reflexive(row_proof),
        }
    }

    /// What `proof` stands for: the composition it names while that is still
    /// unwritten and unsealed, else the variable itself.
    fn composition(&self, proof: &str) -> Composition {
        match self.deferred.get(proof) {
            Some(Deferred::Composed(composition)) if !self.sealed.contains(proof) => {
                composition.clone()
            }
            _ => Composition::Leaf(proof.to_string()),
        }
    }

    /// Name `composition`, holding its row back until something reads the name.
    fn compose(&mut self, composition: Composition) -> String {
        let proof = self.fresh_var();
        self.deferred
            .insert(proof.clone(), Deferred::Composed(composition));
        proof
    }

    /// The connector a built term hands its parent: from the term as written,
    /// through `chain` to the term over canonical children, and back along the
    /// view row `dedup`.
    ///
    /// A term whose own `chain` is still an unwritten composition seals the
    /// connector, so the row above it holds a column here rather than spelling
    /// this term out too. A level's packed row is then a function of its arity
    /// and not of the whole term's size.
    fn level_connector(&mut self, chain: &str, dedup: &str) -> String {
        let composed = matches!(self.deferred.get(chain), Some(Deferred::Composed(_)));
        let connector = self.connect(chain.to_string(), dedup.to_string());
        if composed {
            self.sealed.insert(connector.clone());
        }
        connector
    }

    /// The `@Sym`/`@Trans`/`@Congr` row `composition` is, as a name and its
    /// arguments — `None` unless it is one step over proofs already in scope.
    fn single_step(&self, composition: &Composition) -> Option<(String, String)> {
        let names = self.proof_names();
        Some(match composition {
            Composition::Sym(inner) => {
                (names.eq_sym_constructor.clone(), inner.leaf()?.to_string())
            }
            Composition::Trans(left, right) => (
                names.eq_trans_constructor.clone(),
                format!("{} {}", left.leaf()?, right.leaf()?),
            ),
            Composition::Congr(base, index, child) => (
                names.congr_constructor.clone(),
                format!("{} {index} {}", base.leaf()?, child.leaf()?),
            ),
            Composition::Proj(base, index) => (
                names.proj_constructor.clone(),
                format!("{} {index}", base.leaf()?),
            ),
            Composition::Leaf(_) => return None,
        })
    }

    /// Write the row `proof` names: one `@Sym`/`@Trans`/`@Congr` when the
    /// composition is a single step, else one packed row standing for the whole
    /// of it.
    fn emit_composition(&mut self, stmts: &mut Vec<String>, proof: &str, composition: Composition) {
        let (skeleton, columns) = composition.pack();
        for leaf in &columns {
            self.emit_pending_group(stmts, leaf);
        }
        let (name, args) = self.single_step(&composition).unwrap_or_else(|| {
            let (name, decl) = self.packed_proof_constructor(columns.len());
            if !decl.is_empty() {
                self.pending_decls.push(decl);
            }
            let spelling = skeleton.spelling();
            (name, format!("\"{spelling}\" {}", columns.join(" ")))
        });
        let mint = crate::proofs::proof_fresh::mint_prim_name(&name);
        stmts.push(format!("(let {proof} ({mint} {args}))"));
    }

    /// The declarations the statements written since the last call need, as
    /// commands to run ahead of the ones using them.
    fn take_pending_decls(&mut self) -> Vec<Command> {
        if self.pending_decls.is_empty() {
            return vec![];
        }
        let decls = std::mem::take(&mut self.pending_decls).join("");
        self.parse_program(&decls)
    }

    /// The name of `sort`'s fiat justification, declaring the relation ahead of
    /// the command that first uses it.
    pub(crate) fn fiat_constructor(&mut self, sort: &str) -> String {
        let name = self.proof_names().fiat(sort);
        if self
            .egraph
            .proof_state
            .proof_names
            .fiat_declared
            .insert(sort.to_string())
        {
            let proof = self.proof_sort();
            self.pending_decls.push(format!(
                "(function {name} ({sort} {sort} {proof}) Unit :no-merge :internal-hidden :internal-term-node)\n"
            ));
        }
        name
    }

    /// The name of the primitive projection for a body call taking `args`
    /// arguments, with the declaration emitted ahead of the command using it.
    ///
    /// An argument count is a property of the call sites a program has, not of
    /// the proof format, so the declaration is emitted with the first commands
    /// using it — as [`Self::packed_proof_constructor`] does.
    pub(crate) fn proj_prim_constructor(&mut self, args: usize) -> String {
        let name = self.proof_names().proj_prim(args);
        if !self
            .egraph
            .proof_state
            .proof_names
            .proj_prim_declared
            .insert(args)
        {
            return name;
        }
        let proof = self.proof_sort();
        let columns: String = std::iter::repeat_n(format!("{proof} "), args).collect();
        self.pending_decls.push(format!(
            "(function {name} (String i64 {columns}{proof}) Unit :no-merge :internal-hidden :internal-term-node)\n"
        ));
        name
    }

    /// The name of `func`'s subsumption marker relation, declaring the marker
    /// and its maintenance rules ahead of the command that first uses them.
    fn subsume_marker(&mut self, func: &str, input: &[ArcSort]) -> String {
        if self
            .egraph
            .proof_state
            .proof_names
            .subsume_declared
            .insert(func.to_string())
        {
            let decls = self.subsume_scaffolding(func, input);
            self.pending_decls.push(decls);
        }
        self.subsumed_name(func)
    }

    /// Hold back `group`, the statements binding `proof`, until something reads
    /// `proof`. A proof that nothing ends up reading is never bound, and
    /// [`Self::drop_pending_lookups`] discards it.
    ///
    /// `group` is emitted verbatim wherever the flush lands, so everything it
    /// reads must be either bound within it or in scope there — a query
    /// variable, or a statement already emitted.
    pub(crate) fn defer_lookup(&mut self, proof: &str, group: Vec<String>) {
        self.defer_lookup_reading(proof, group, vec![]);
    }

    /// [`Self::defer_lookup`] for a group standing on other held-back proofs,
    /// which are emitted ahead of it wherever it lands.
    pub(crate) fn defer_lookup_reading(
        &mut self,
        proof: &str,
        stmts: Vec<String>,
        reads: Vec<String>,
    ) {
        self.deferred
            .insert(proof.to_string(), Deferred::Stmts { stmts, reads });
    }

    /// Discard everything still held back, whose proofs nothing read.
    pub(crate) fn drop_pending_lookups(&mut self) {
        self.deferred.clear();
        self.sealed.clear();
        self.unanchored.clear();
    }

    /// Emit the deferred groups `args_joined` reads, and transitively the groups
    /// those read, keeping each binding ahead of the statement reading it. A
    /// group is emitted at most once, wherever it is first read.
    fn emit_pending_lookups(&mut self, stmts: &mut Vec<String>, args_joined: &str) {
        if self.deferred.is_empty() && self.unanchored.is_empty() {
            return;
        }
        for var in read_vars(args_joined) {
            self.emit_pending_group(stmts, var);
        }
    }

    /// [`Self::emit_pending_lookups`] for what one variable holds back. Called
    /// directly by a reader that does not go through [`Self::mint`] — a statement
    /// built by `format!` rather than as a row of its own.
    fn emit_pending_group(&mut self, stmts: &mut Vec<String>, var: &str) {
        match self.deferred.remove(var) {
            Some(Deferred::Composed(composition)) => self.emit_composition(stmts, var, composition),
            Some(Deferred::Stmts {
                stmts: group,
                reads,
            }) => {
                for read in reads {
                    self.emit_pending_group(stmts, &read);
                }
                stmts.extend(group);
            }
            None => {
                assert!(
                    !self.unanchored.contains_key(var),
                    "internal invariant: the body variable `{}` has no reflexive anchor — a value \
                     the query computed rather than one a view row names. Proof support should \
                     have rejected the rule before it was encoded.",
                    self.unanchored[var]
                );
            }
        }
    }

    /// Bind a fresh id of `sort`, asserting nothing about it.
    fn fresh_id(&mut self, stmts: &mut Vec<String>, sort: &str) -> String {
        let v = self.fresh_var();
        // The generic `get-fresh!` takes the target sort as a string literal so it
        // types its output without per-sort primitives (its runtime ignores the arg).
        let get_fresh = crate::proofs::proof_fresh::GET_FRESH_PRIM_NAME;
        stmts.push(format!("(let {v} ({get_fresh} \"{sort}\"))"));
        v
    }

    /// Append the one statement minting a fresh id and asserting the relation
    /// row `({name} {args_joined} <fresh>)`, returning the fresh variable.
    /// Every minted id keeps its row: nothing is ever merged away.
    pub(crate) fn mint(
        &mut self,
        stmts: &mut Vec<String>,
        name: &str,
        args_joined: &str,
    ) -> String {
        self.emit_pending_lookups(stmts, args_joined);
        let v = self.fresh_var();
        let mint = crate::proofs::proof_fresh::mint_prim_name(name);
        let sep = if args_joined.is_empty() { "" } else { " " };
        stmts.push(format!("(let {v} ({mint}{sep}{args_joined}))"));
        v
    }

    /// Read an encoded global's value from its FD view `() -> (val, proof)`, for a
    /// global reference `(x)` appearing in an action. `set-if-empty` returns the
    /// stored e-class (a global is `set` before it is used, so the fresh fallback is
    /// dead code that only fires on a malformed program). The value read is already
    /// the view's canonical e-class, so no natural/deduped connector is recorded.
    ///
    /// The signature requires the fallback pair, so both are bare fresh ids: no
    /// row says anything about either, since nothing ever reads them.
    fn lookup_global(&mut self, name: &str, res: &mut Vec<String>) -> String {
        let view = self.view_name(name);
        let set_if_empty = crate::proofs::proof_fresh::set_if_empty_prim_name(&view);
        let view_sort = self.term_sort(name);
        let fresh_e = self.fresh_id(res, &view_sort);
        let fallback_proof = if self.proofs_enabled() {
            let proof_sort = self.proof_sort();
            self.fresh_id(res, &proof_sort)
        } else {
            "()".to_string()
        };
        let vx = self.fresh_var();
        res.push(format!(
            "(let {vx} ({set_if_empty} {fresh_e} {fallback_proof}))"
        ));
        vx
    }

    /// The `Proof` datatype's sort name.
    pub(crate) fn proof_sort(&self) -> String {
        self.proof_names().proof_datatype.clone()
    }

    /// The sort of `fname`'s e-class, which its term rows are minted into (see
    /// [`Self::term_and_view`]).
    fn term_sort(&self, fname: &str) -> String {
        self.proof_names()
            .fn_to_term_sort
            .get(fname)
            .expect("term sort recorded in term_and_view")
            .clone()
    }

    /// Add to the term and view tables, returning the created term. For
    /// constructors, `args` excludes the eclass of the resulting term (it may not
    /// exist yet); for custom functions, `args` includes all arguments, output
    /// included.
    ///
    /// `run` is the columns the caller claimed for the position it is at; only a
    /// constructor reads past the own conclusion the caller already named.
    fn add_term_and_view(
        &mut self,
        emit: &mut Emit,
        func_type: &FuncType,
        args: &[Operand],
        run: Option<HeadRun>,
    ) -> Operand {
        if func_type.subtype != FunctionSubtype::Constructor {
            let fv = self.add_custom_row(emit, func_type, &ids(args));
            Operand::plain(fv)
        } else if !self.egraph.proof_state.proofs_enabled {
            let canon = self.add_constructor_term_only(emit.stmts, func_type, &ids(args));
            Operand::plain(canon)
        } else {
            self.add_constructor_with_proof(emit, func_type, args, run)
        }
    }

    /// Custom functions: mint the term-relation row and update the FD view. No
    /// canonicalization threading.
    fn add_custom_row(&mut self, emit: &mut Emit, func_type: &FuncType, args: &[String]) -> String {
        let fv = self.mint(
            emit.stmts,
            &func_type.name,
            &ListDisplay(args, " ").to_string(),
        );
        let view_proof_var = if self.egraph.proof_state.proofs_enabled {
            let sort = self.term_sort(&func_type.name);
            self.reflexive_for_justification(emit, &fv, &sort)
        } else {
            "()".to_string()
        };
        // `args` ends with the output value (from the `(set (f c..) v)` action);
        // the FD view is keyed on the children. `view_proof_var` proves the row's
        // f-application term `f(children, output)` (what `fv` extracts to) — the
        // premise `MergeRow`/`MergeIdx` reconstruct their conclusion from.
        let (output, children) = args.split_last().expect("custom set needs an output");
        let update = self.update_fd_view(&func_type.name, children, output, &view_proof_var);
        emit.stmts.push(update);
        fv
    }

    /// Term-only constructors: build the term with canonical children and
    /// canonicalize it to the view's e-class via `set-if-empty`; return that
    /// canonical id so parents build with canonical children (views stay
    /// canonical).
    fn add_constructor_term_only(
        &mut self,
        res: &mut Vec<String>,
        func_type: &FuncType,
        args: &[String],
    ) -> String {
        let view = self.view_name(&func_type.name);
        let set_if_empty = crate::proofs::proof_fresh::set_if_empty_prim_name(&view);
        let fv = self.mint(res, &func_type.name, &ListDisplay(args, " ").to_string());
        let canon = self.fresh_var();
        res.push(format!(
            "(let {canon} ({set_if_empty} {} {fv} ()))",
            ListDisplay(args, " ")
        ));
        canon
    }

    /// Mint a constructor's natural node and the proofs about it.
    fn build_natural_with_congr(
        &mut self,
        emit: &mut Emit,
        fname: &str,
        args: &[Operand],
    ) -> Natural {
        let sort = self.term_sort(fname);
        let nat_args: Vec<String> = args.iter().map(|a| a.natural.clone()).collect();
        let dedup_args = ids(args);
        let fv_nat = self.mint(emit.stmts, fname, &ListDisplay(&nat_args, " ").to_string());
        // The head's own conclusion here is only ever read by the congruence
        // chain below, so a head that numbers its proofs instead of composing
        // them writes no row for it: conversion recovers it from the column.
        let to_dedup = emit.head.composes().then(|| {
            let nat_prf = self.reflexive_for_justification(emit, &fv_nat, &sort);
            let mut steps = vec![];
            for (i, arg) in args.iter().enumerate() {
                if let Some(conn) = &arg.connector {
                    steps.push((i, self.connector_node(emit, conn)));
                }
            }
            self.canonicalize(nat_prf, steps)
        });
        Natural {
            dedup_args,
            fv_nat,
            to_dedup,
        }
    }

    /// Proof-mode constructors: build the *natural* term (children at their
    /// as-built ids) and the *canonical* term (children at their view-deduped
    /// ids), connect them with a `Congr` chain over the changed children, then
    /// `set-if-empty` to the view's deduped e-class and stitch on the view-dedup
    /// edge. The operand returned reads as the deduped e-class (so parents and
    /// views stay canonical), carrying the natural term and the connector
    /// `natural = deduped` for the parent's `Congr` and the root `union`.
    ///
    /// `run` is the [`HeadPosition::Built`] columns the caller claimed.
    fn add_constructor_with_proof(
        &mut self,
        emit: &mut Emit,
        func_type: &FuncType,
        args: &[Operand],
        run: Option<HeadRun>,
    ) -> Operand {
        let view = self.view_name(&func_type.name);
        let set_if_empty = crate::proofs::proof_fresh::set_if_empty_prim_name(&view);

        // `fv_nat` stays *unseeded* — only `fv_can` is written to the view — so the
        // view's congruence `:merge` can never move it, and the proof of the shape the
        // head wrote stays stated over the ids the head built. `fv_can` is a separate
        // node even when no child changed.
        let Natural {
            dedup_args,
            fv_nat,
            to_dedup,
        } = self.build_natural_with_congr(emit, &func_type.name, args);
        let fv_can = self.mint(
            emit.stmts,
            &func_type.name,
            &ListDisplay(&dedup_args, " ").to_string(),
        );
        let can_prf = match &to_dedup {
            Some(chain) => self.reflexive(chain.clone()),
            // One row records the composition proof conversion rebuilds.
            None => {
                let canonical = emit
                    .justification
                    .at(head_column(run, HeadProof::Canonical));
                self.rule_row(&mut emit.justified_by(&canonical))
            }
        };

        // Dedup `fv_can` to the view e-class and read the view's stored proof
        // (`dedup = f(children)`).
        let dedup = self.fresh_var();
        let vprf = self.fresh_var();
        let view_proof = crate::proofs::proof_fresh::view_proof_prim_name(&view);
        let dedup_args = ListDisplay(&dedup_args, " ");
        // The two statements below read `can_prf` directly, not through a mint.
        self.emit_pending_group(emit.stmts, &can_prf);
        emit.stmts.push(format!(
            "(let {dedup} ({set_if_empty} {dedup_args} {fv_can} {can_prf}))"
        ));
        emit.stmts.push(format!(
            "(let {vprf} ({view_proof} {dedup_args} {can_prf}))"
        ));
        // The read misses on a row this action just seeded, returning the fallback:
        // a proof about the term as written rather than about the canonical one,
        // which is how conversion tells "no bridge" from a real one.
        emit.head.record_bridge(&vprf);

        let connector = match &to_dedup {
            Some(chain) => Connector::Node(self.level_connector(chain, &vprf)),
            None => Connector::Column(
                run.expect("a rule head's terms are numbered")
                    .column(HeadProof::Connector),
            ),
        };
        Operand::built(dedup, fv_nat, connector)
    }

    /// Declare one index per distinct eq-sort among a view's columns, so an `@UF`
    /// edge on a term reaches the rows mentioning it by lookup instead of by
    /// matching the view once per column. The e-class column is indexed too, so a
    /// stale e-class is found the same way. Containers are excluded: they carry
    /// no `@UF` row and are canonicalized structurally.
    fn declare_view_indexes(&mut self, fdecl: &ResolvedFunctionDecl) -> String {
        let types = fdecl.resolved_schema.view_types();
        // Children, plus the value column when it is an e-class. When only the
        // e-class moves the canonical key equals the old one, so the rebuild rule
        // deletes the old row before re-inserting rather than after (see
        // `indexed_rebuild_rule`). A custom function's value column is an ordinary
        // output, rebuilt by its own rule, so indexing it would only invite the
        // whole-row rule to rewrite it with an e-class's proof shape.
        let indexable = if self.output_is_eclass(fdecl) {
            types.len()
        } else {
            types.len() - 1
        };
        let mut by_sort: Vec<(String, Vec<usize>)> = Vec::new();
        for (i, ty) in types[..indexable].iter().enumerate() {
            if ty.is_eq_container_sort() || !ty.is_eq_sort() {
                continue;
            }
            let sort = ty.name().to_string();
            match by_sort.iter_mut().find(|(s, _)| *s == sort) {
                Some((_, positions)) => positions.push(i),
                None => by_sort.push((sort, vec![i])),
            }
        }
        let view_name = self.view_name(&fdecl.name);
        let mut decls = String::new();
        let mut entries = Vec::new();
        for (sort_name, positions) in by_sort {
            let index_name = self
                .egraph
                .parser
                .symbol_gen
                .fresh(&format!("{}Occ_{sort_name}", fdecl.name));
            decls.push_str(&format!(
                "(index {index_name} {view_name} (any {}))\n",
                ListDisplay(&positions, " ")
            ));
            entries.push(ViewIndex {
                name: index_name,
                sort_name,
            });
        }
        self.egraph
            .proof_state
            .view_index
            .insert(fdecl.name.clone(), entries);
        decls
    }

    /// Query a functional-dependency view by its `children` key, binding fresh
    /// variables for the value and proof output columns:
    /// `(= (values v pf) (@FView children))`. The value is the e-class for
    /// constructors/globals and the function output for custom `:merge` views.
    /// Returns `(query, value_var, proof_var)`.
    pub(super) fn query_fd_view(
        &mut self,
        fname: &str,
        children: &[String],
    ) -> (String, String, String) {
        let view_name = self.view_name(fname);
        let value_var = self.fresh_var();
        let pf_var = self.fresh_var();
        let query = format!(
            "(= (values {value_var} {pf_var}) ({view_name} {}))",
            ListDisplay(children, " ")
        );
        (query, value_var, pf_var)
    }

    /// Rebuild a custom function's merge body inside its FD view's `:merge` (see
    /// [`Self::custom_view_merge`]), minting each constructor subterm via
    /// `add_term_and_view` (so canonical ids are used, like every other term site)
    /// with a term-free `MergeIdx` proof. `idx` is threaded pre-order (incremented
    /// once per node, leaves included) to match the checker's `subexpr_at_index`,
    /// so subexpr `idx` evaluated on the premise outputs reconstructs exactly this
    /// node's term. `old`/`new` in the body map to the `:merge` output columns
    /// `old0`/`new0`; the carried view proofs are `old1`/`new1`.
    fn instrument_merge_body(
        &mut self,
        emit: &mut Emit,
        expr: &ResolvedExpr,
        fname: &str,
        idx: &mut usize,
    ) -> Operand {
        let node = merge_idx(fname, *idx);
        *idx += 1;
        match expr {
            ResolvedExpr::Lit(_, lit) => Operand::plain(format!("{lit}")),
            ResolvedExpr::Var(_, resolved_var) => {
                Operand::plain(match resolved_var.name.as_str() {
                    "old" => "old0".to_string(),
                    "new" => "new0".to_string(),
                    other => other.to_string(),
                })
            }
            ResolvedExpr::Call(_, ResolvedCall::Func(func_type), args) => {
                let arg_vars = args
                    .iter()
                    .map(|a| self.instrument_merge_body(emit, a, fname, idx))
                    .collect::<Vec<_>>();
                self.add_term_and_view(&mut emit.justified_by(&node), func_type, &arg_vars, None)
            }
            // A container-producing primitive (e.g. `set-intersect`): build the
            // container over the recursively-built args.
            ResolvedExpr::Call(_, ResolvedCall::Primitive(sp), args) => {
                let arg_vars = args
                    .iter()
                    .map(|a| self.instrument_merge_body(emit, a, fname, idx))
                    .collect::<Vec<_>>();
                let prim_name = sp.name().to_string();
                let fv = self.fresh_var();
                emit.stmts.push(format!(
                    "(let {fv} ({prim_name} {}))",
                    ListDisplay(ids(&arg_vars), " ")
                ));
                Operand::plain(fv)
            }
            ResolvedExpr::Call(_, _, _) => {
                panic!("proof-mode merge body for `{fname}` contains an unsupported call form")
            }
        }
    }

    // Add to view and term tables, returning a variable for the created term.
    //
    // A call claims its columns after its arguments have claimed theirs, so the
    // walk numbers a term's children before the term (see
    // [`crate::proofs::proof_head`]).
    fn instrument_action_expr(
        &mut self,
        expr: &ResolvedExpr,
        emit: &mut Emit,
        scope: &Scope,
    ) -> Operand {
        match expr {
            ResolvedExpr::Lit(_, lit) => Operand::plain(format!("{lit}")),
            ResolvedExpr::Var(_, resolved_var) => scope.read(&resolved_var.name),
            ResolvedExpr::Call(_, resolved_call, args) => {
                let args = args
                    .iter()
                    .map(|arg| self.instrument_action_expr(arg, emit, scope))
                    .collect::<Vec<_>>();
                // The whole run this call claims, its own conclusion first.
                let run = emit.head.claim(match constructor_operand(expr) {
                    Some(_) => HeadPosition::Built,
                    None => HeadPosition::Call,
                });
                let own = emit.justification.at(head_column(run, HeadProof::Own));
                let emit = &mut emit.justified_by(&own);
                match resolved_call {
                    ResolvedCall::Func(func_type) => {
                        if func_type.subtype == FunctionSubtype::Custom {
                            // Proof normal form bans looking up custom functions in
                            // actions, except encoded globals: a nullary
                            // `:internal-let` function whose value is read from its
                            // FD view (see `lookup_global`). This is the only custom
                            // lookup allowed here.
                            if self.egraph.type_info.is_global(&func_type.name) {
                                Operand::plain(self.lookup_global(&func_type.name, emit.stmts))
                            } else {
                                panic!(
                                    "Found a function lookup in actions, should have been prevented by typechecking"
                                )
                            }
                        } else {
                            self.add_term_and_view(emit, func_type, &args, run)
                        }
                    }
                    ResolvedCall::Primitive(specialized_primitive) => {
                        let prim_name = specialized_primitive.name().to_string();
                        let out = specialized_primitive.output();
                        let container_proof =
                            self.egraph.proof_state.proofs_enabled && out.is_eq_container_sort();
                        // Build a container over *natural* element ids where we have
                        // them (an eq-sort arg with a connector), recording each
                        // `natural -> (deduped, connector)` edge in the element's
                        // union-find. The container then extracts the syntactic
                        // shape the rule wrote, and the ordinary container rebuild
                        // canonicalizes the element (see "Containers" in
                        // proof_encoding.md).
                        let mut build_args = Vec::with_capacity(args.len());
                        for (arg, asort) in args.iter().zip(specialized_primitive.input()) {
                            match &arg.connector {
                                Some(connector) if container_proof && asort.is_eq_sort() => {
                                    let (value, natural) = (&arg.value, &arg.natural);
                                    let uf = self.uf_name(asort.name());
                                    let conn = self.connector_node(emit, connector);
                                    // The `@UF` row reads the connector directly,
                                    // not through a mint.
                                    self.emit_pending_group(emit.stmts, &conn);
                                    emit.stmts.push(format!(
                                        "(set ({uf} {natural}) (values {value} {conn}))"
                                    ));
                                    build_args.push(natural.clone());
                                }
                                _ => build_args.push(arg.value.clone()),
                            }
                        }
                        let fv = self.fresh_var();
                        emit.stmts.push(format!(
                            "(let {fv} ({prim_name} {}))",
                            ListDisplay(&build_args, " ")
                        ));
                        Operand::plain(fv)
                    }
                    ResolvedCall::Values(_) => {
                        panic!("tuple-output (`values`) functions are not supported in proofs")
                    }
                }
            }
        }
    }

    /// In proof mode, rule_proof justifies the actions taken.
    fn instrument_actions(
        &mut self,
        actions: &[ResolvedAction],
        justification: &Justification,
    ) -> Vec<String> {
        // Normalize union operands to variables, then build each
        // freshly-constructed union operand directly into the other operand's
        // e-class (see proof_encoding.md, "Union in a rule").
        let symbol_gen = &mut self.egraph.parser.symbol_gen;
        let mut fresh = || symbol_gen.fresh("union_operand");
        let plan = HeadPlan::new(actions, &mut fresh);
        // A rule head is a format proof conversion can replay, so its proofs are
        // named by column; everywhere else the encoder composes them itself.
        let mut head = match justification {
            Justification::Rule(..) => Head::skeleton(plan.layout.clone()),
            _ => Head::composed(),
        };
        let mut scope = Scope::default();
        let mut res = vec![];
        let mut emit = Emit {
            stmts: &mut res,
            head: &mut head,
            justification,
        };
        for (i, action) in plan.actions.iter().enumerate() {
            if plan.dropped.contains(&i) {
                continue;
            }
            match action {
                ResolvedAction::Let(_, v, expr) if plan.construct_into.contains_key(&v.name) => {
                    let target = scope.read(&plan.construct_into[&v.name]);
                    let guest = self.instrument_construct_into(&mut emit, expr, &target, &scope);
                    emit.stmts.push(format!("(let {} {})", v.name, guest.value));
                    scope.bind(&v.name, &guest);
                }
                _ => self.instrument_action(action, &mut emit, &mut scope),
            }
        }
        res
    }

    /// Instrument a rule to use term encoding: the body reads the view tables,
    /// and the actions write the term and view rows. With proofs enabled the
    /// actions also build the rule's proofs, one of which fills each written
    /// row's proof column.
    fn instrument_rule(&mut self, rule: &ResolvedRule) -> Vec<Command> {
        // The reflexive-proof names are globally fresh, so keeping earlier rules'
        // would be harmless but unbounded.
        self.reflexive.clear();
        // Named before the body is walked: an element anchor records the rule its
        // reading call sits in.
        let rule_name_var = if self.egraph.proof_state.proofs_enabled {
            self.egraph.parser.symbol_gen.fresh("rule_name")
        } else {
            "()".to_string()
        };
        let body_rule = self
            .egraph
            .proof_state
            .proofs_enabled
            .then_some(rule_name_var.as_str());
        let (facts, action_lookups, premises) = self.instrument_facts_in(&rule.body, body_rule);
        // Every mint site replaces the placeholder with the column the walk is at.
        let proof = Justification::Rule(rule_name_var.clone(), premises, HeadColumn::Unnumbered);
        // A proof-mode head reads the database: it interns each subterm it builds
        // and reads back the view row's committed proof, so it needs a Read/Full
        // action context (`eval_opt` below).
        let reads_in_rhs = self.egraph.proof_state.proofs_enabled;
        let action_lookups_str = ListDisplay(&action_lookups, "\n                    ");
        let proof_prelude = if self.egraph.proof_state.proofs_enabled {
            format!(
                "(let {rule_name_var} \"{}\")
                 {action_lookups_str}",
                rule.name
            )
        } else {
            "".to_string()
        };

        let actions = self.instrument_actions(&rule.head.0, &proof);
        // A premise proof and the lookups under it are emitted by the first
        // statement naming them, which is a head row; whatever is still deferred
        // reached none, so the rule never needs to compute it.
        self.drop_pending_lookups();
        let name = &rule.name;
        let ruleset_opt = if rule.ruleset.is_empty() {
            "".to_string()
        } else {
            format!(":ruleset {}", rule.ruleset)
        };
        // Preserve a user `:naive` (else it silently reverts to seminaive).
        // Otherwise an RHS-reading rule needs `:unsafe-seminaive` (or `:naive`
        // under the test knob).
        let eval_opt = if rule.eval_mode.is_naive() {
            ":naive"
        } else if reads_in_rhs {
            self.rhs_read_eval_opt()
        } else {
            ""
        };
        let instrumented = format!(
            "(rule ({})
                   ({proof_prelude}
                    {})
                    {ruleset_opt} {eval_opt}
                    :name \"{name}\")",
            ListDisplay(facts, " "),
            ListDisplay(actions, " "),
        );
        self.parse_program(&instrumented)
    }

    /// Any schedule should be sound as long as we saturate.
    fn rebuild(&mut self) -> Schedule {
        let path_compress_ruleset = self.proof_names().path_compress_ruleset_name.clone();
        let rebuilding_cleanup_ruleset = self.proof_names().rebuilding_cleanup_ruleset_name.clone();
        let rebuilding_ruleset = self.proof_names().rebuilding_ruleset_name.clone();
        let subsume_ruleset = self.proof_names().subsume_ruleset_name.clone();
        // The `@UF` `:merge` resolves conflicting parents itself, so only
        // `path_compress` (flattening chains) remains as UF maintenance.
        self.parse_schedule(format!(
            "(seq
              (saturate
                  {rebuilding_cleanup_ruleset}
                  (saturate {path_compress_ruleset})
                  {rebuilding_ruleset})
              {subsume_ruleset})"
        ))
    }

    fn instrument_schedule(&mut self, schedule: &ResolvedSchedule) -> Schedule {
        match schedule {
            ResolvedSchedule::Run(span, config) => {
                let new_run = match config.until {
                    Some(ref facts) => {
                        let (instrumented, _lookups, _premises) = self.instrument_facts(facts);
                        self.drop_pending_lookups();
                        let instrumented_facts = self.parse_facts(&instrumented);
                        Schedule::Run(
                            span.clone(),
                            RunConfig {
                                ruleset: config.ruleset.clone(),
                                until: Some(instrumented_facts),
                            },
                        )
                    }
                    None => Schedule::Run(
                        span.clone(),
                        RunConfig {
                            ruleset: config.ruleset.clone(),
                            until: None,
                        },
                    ),
                };
                Schedule::Sequence(span.clone(), vec![new_run, self.rebuild()])
            }
            ResolvedSchedule::Sequence(span, schedules) => Schedule::Sequence(
                span.clone(),
                schedules
                    .iter()
                    .map(|s| self.instrument_schedule(s))
                    .collect(),
            ),
            ResolvedSchedule::Saturate(span, schedule) => {
                Schedule::Saturate(span.clone(), Box::new(self.instrument_schedule(schedule)))
            }
            GenericSchedule::Repeat(span, n, schedule) => Schedule::Repeat(
                span.clone(),
                *n,
                Box::new(self.instrument_schedule(schedule)),
            ),
        }
    }

    fn input_actions(
        egraph: &EGraph,
        span: &Span,
        name: &str,
        file: &str,
    ) -> Result<Vec<ResolvedAction>, Error> {
        let function_type = egraph
            .proof_state
            .original_typechecking
            .as_ref()
            .and_then(|typechecker| typechecker.type_info.get_func_type(name))
            .unwrap_or_else(|| panic!("Unrecognized function name {name}"))
            .clone();
        let rows =
            EGraph::read_input_file(egraph.fact_directory.as_deref(), &function_type, span, file)?;
        let mut actions = vec![];
        for row in rows {
            let mut expressions = row
                .into_iter()
                .map(|literal| ResolvedExpr::Lit(span.clone(), literal));
            let inputs = expressions
                .by_ref()
                .take(function_type.input.len())
                .collect::<Vec<_>>();
            actions.push(if function_type.subtype == FunctionSubtype::Constructor {
                ResolvedAction::Expr(
                    span.clone(),
                    ResolvedExpr::Call(
                        span.clone(),
                        ResolvedCall::Func(function_type.clone()),
                        inputs,
                    ),
                )
            } else {
                let output = expressions
                    .next()
                    .expect("custom input row must contain its output value");
                ResolvedAction::Set(
                    span.clone(),
                    ResolvedCall::Func(function_type.clone()),
                    inputs,
                    output,
                )
            });
        }
        Ok(actions)
    }

    fn term_encode_command(
        &mut self,
        command: &ResolvedNCommand,
        res: &mut Vec<Command>,
    ) -> Result<(), Error> {
        log::trace!("Term encoding for {command}");
        match &command {
            ResolvedNCommand::Sort {
                span,
                name,
                presort_and_args,
                unionable,
                ..
            } => {
                // After the proof-encoding gate, any sort carrying a presort
                // is one of the supported container sorts. Containers have no
                // per-sort union-find (they are canonicalized structurally),
                // so they get `uf: None` and `find_canonical` leaves their
                // value unchanged during extraction.
                let is_container = presort_and_args.is_some();
                let uf_name = if is_container {
                    None
                } else {
                    Some((self.uf_name(name), None))
                };
                // For container sorts, build the rebuild-primitive spec now (it
                // generates and caches the fresh primitive names used by the
                // rebuild rules below) and attach it as an annotation so the
                // primitives can be re-registered when this desugared Sort
                // command is typechecked / re-parsed.
                let container_rebuild = if is_container {
                    let container_sort = self
                        .egraph
                        .proof_state
                        .original_typechecking
                        .as_ref()
                        .and_then(|tc| tc.get_sort_by_name(name).cloned())
                        .unwrap_or_else(|| {
                            panic!("container sort {name} not found while term-encoding")
                        });
                    Some(self.build_container_rebuild_spec(&container_sort))
                } else {
                    None
                };
                res.push(Command::Sort {
                    span: span.clone(),
                    name: name.clone(),
                    presort_and_args: presort_and_args.clone(),
                    uf: uf_name,
                    unionable: *unionable,
                    container_rebuild,
                    // The Proof sort (which carries :internal-proof-names) is
                    // emitted as source by the proof header, not here.
                    proof_constructors: None,
                });
                res.extend(self.declare_sort(name, is_container));
            }
            ResolvedNCommand::Function(fdecl) => {
                res.extend(self.term_and_view(fdecl));
                res.extend(self.rebuilding_rules(fdecl));
            }
            ResolvedNCommand::NormRule { rule } => {
                res.extend(self.instrument_rule(rule));
            }
            // A top-level action, or a block of them. The instrumented result
            // runs as one local-scope block so the minted temporaries stay
            // local (see `parse_program_as_local_actions`).
            ResolvedNCommand::CoreAction(_) | ResolvedNCommand::CoreActions(_) => {
                let actions: &[ResolvedAction] = match command {
                    ResolvedNCommand::CoreAction(action) => std::slice::from_ref(action),
                    ResolvedNCommand::CoreActions(actions) => &actions.0,
                    _ => unreachable!("guarded by the match arm"),
                };
                let instrumented = self
                    .instrument_actions(actions, &Justification::Fiat)
                    .join("\n");
                // A term built here records a connector nothing may go on to
                // compose with; whatever is still deferred reached no statement.
                self.drop_pending_lookups();
                res.extend(self.parse_program_as_local_actions(&instrumented));
            }
            ResolvedNCommand::LetBegin(..) => {
                unreachable!("LetBegin is removed by remove_globals")
            }
            ResolvedNCommand::Check(span, facts) => {
                let (instrumented, _lookups, _premises) = self.instrument_facts(facts);
                self.drop_pending_lookups();
                res.push(Command::Check(
                    span.clone(),
                    self.parse_facts(&instrumented),
                ));
            }
            ResolvedNCommand::RunSchedule(schedule) => {
                res.push(Command::RunSchedule(self.instrument_schedule(schedule)));
            }
            ResolvedNCommand::Fail(span, cmds) => {
                // Encode every wrapped command and keep the whole flattened result
                // inside one `fail` (a single command can encode to several).
                let mut encoded = vec![];
                for cmd in cmds {
                    self.term_encode_command(cmd, &mut encoded)?;
                }
                res.push(Command::Fail(span.clone(), encoded));
            }
            ResolvedNCommand::Input { name, .. } => {
                // Loaded natively at run time (see `EGraph::native_input`), inserting
                // straight into the encoded tables. Pass the command through so
                // `run_command` dispatches it. The load writes a reflexive fiat per
                // row, so the loaded sort's fiat relation has to be declared here:
                // nothing the encoder emits mentions it.
                if self.proofs_enabled() {
                    let sort = self.term_sort(name);
                    self.fiat_constructor(&sort);
                }
                res.push(command.to_command().make_unresolved());
            }
            ResolvedNCommand::Extract(span, expr, variants) => {
                // Instrument the expressions to use view tables (like actions, not facts)
                let mut action_stmts = vec![];
                // An extract expression binds nothing, so no name it reads can
                // stand for a term built here, and it is no rule head.
                let scope = Scope::default();
                let mut head = Head::composed();
                let fiat = Justification::Fiat;
                let mut emit = Emit {
                    stmts: &mut action_stmts,
                    head: &mut head,
                    justification: &fiat,
                };
                let instrumented_expr = self.instrument_action_expr(expr, &mut emit, &scope).value;
                let instrumented_variants = self
                    .instrument_action_expr(variants, &mut emit, &scope)
                    .value;

                // Add any action statements needed to set up the expressions
                for stmt in action_stmts {
                    res.extend(self.parse_program(&stmt));
                }
                // Rebuild before extract; we may have added new view rows that need canonicalization
                res.push(Command::RunSchedule(self.rebuild()));
                res.push(Command::Extract(
                    span.clone(),
                    self.parse_expr(&instrumented_expr),
                    self.parse_expr(&instrumented_variants),
                ));
            }
            ResolvedNCommand::PrintSize(span, name) => {
                // In proof mode, print the size of the view table for constructors
                let new_name = name.as_ref().map(|n| {
                    if self
                        .egraph
                        .type_info
                        .get_func_type(n)
                        .is_some_and(|f| f.subtype == FunctionSubtype::Constructor)
                    {
                        self.view_name(n)
                    } else {
                        n.clone()
                    }
                });
                res.push(Command::PrintSize(span.clone(), new_name));
            }
            ResolvedNCommand::Pop(..)
            | ResolvedNCommand::Push(..)
            | ResolvedNCommand::Index { .. }
            | ResolvedNCommand::AddRuleset(..)
            | ResolvedNCommand::Output { .. }
            | ResolvedNCommand::UnstableCombinedRuleset(..)
            | ResolvedNCommand::PrintOverallStatistics(..)
            | ResolvedNCommand::PrintFunction(..)
            | ResolvedNCommand::ProveExists(..) => {
                res.push(command.to_command().make_unresolved());
            }
            ResolvedNCommand::UserDefined(..) => {
                panic!("User defined commands unsupported in term encoding");
            }
        }
        Ok(())
    }

    pub(crate) fn add_term_encoding_helper(
        &mut self,
        program: Vec<ResolvedNCommand>,
    ) -> Result<Vec<Command>, Error> {
        let mut res = vec![];

        if !self.egraph.proof_state.term_header_added {
            res.extend(self.term_header());
            if self.egraph.proof_state.proofs_enabled {
                let proof_header = self.proof_header();
                res.extend(self.parse_program(&proof_header));
            }
            self.egraph.proof_state.term_header_added = true;
        }
        if self.egraph.proof_state.proofs_enabled {
            let arities = self.rule_arity_header(&program);
            res.extend(arities);
        }

        for command in program {
            let at = res.len();
            self.term_encode_command(&command, &mut res)?;
            // A packed constructor and a subsumption marker are properties of the
            // statements written, so each is declared with the first command using
            // it — ahead of that command, and outside any `fail` wrapping it.
            res.splice(at..at, self.take_pending_decls());

            if !command_skips_rebuild(&command) {
                res.push(Command::RunSchedule(self.rebuild()));
            }
        }

        Ok(res)
    }
}

/// Whether no maintenance rebuild is needed after `command`.
///
/// Declarations (sorts, functions, rules) run no actions. A `set` (including a
/// global-let's `(set (g) e)`), a `let`, or a top-level expression over
/// non-container sorts builds and dedups terms via `set-if-empty` without
/// merging e-classes or deferring work, so no maintenance rebuild is needed
/// after it — this is what stops N global-let `set`s from each triggering a
/// rebuild (quadratic). A block skips when all of its actions do.
/// Everything else still rebuilds: `union` merges e-classes, `subsume` defers
/// work to the maintenance ruleset, `delete` drops a row other rows may be
/// stale against, and a container-valued action needs the (`:naive`) container
/// rebuild to recanonicalize it — all need the following rebuild to run.
fn command_skips_rebuild(command: &ResolvedNCommand) -> bool {
    fn touches_container(e: &ResolvedExpr) -> bool {
        e.output_type().is_eq_container_sort()
            || matches!(e, ResolvedExpr::Call(_, _, args) if args.iter().any(touches_container))
    }
    fn action_skips_rebuild(action: &ResolvedAction) -> bool {
        match action {
            ResolvedAction::Expr(_, e) | ResolvedAction::Let(_, _, e) => !touches_container(e),
            ResolvedAction::Set(_, _, args, rhs) => !args
                .iter()
                .chain(std::iter::once(rhs))
                .any(touches_container),
            _ => false,
        }
    }
    match command {
        ResolvedNCommand::Function(..)
        | ResolvedNCommand::NormRule { .. }
        | ResolvedNCommand::Sort { .. } => true,
        ResolvedNCommand::CoreAction(action) => action_skips_rebuild(action),
        ResolvedNCommand::CoreActions(actions) => actions.0.iter().all(action_skips_rebuild),
        _ => false,
    }
}
