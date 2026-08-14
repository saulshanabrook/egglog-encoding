//! Proof encoding helper functions that handle
//! naming, headers, and checking whether a program supports proof encoding.

use std::path::Path;
use std::sync::{Arc, Mutex};

use crate::{
    ArcSort, EGraph, TypeInfo, Value,
    ast::{
        Command, Expr, Fact, GenericCommand, ResolvedAction, ResolvedCommand, ResolvedExpr,
        ResolvedExprExt, ResolvedFact, ResolvedNCommand, Schedule, Span,
    },
    core::ResolvedCall,
    proofs::{proof_checker::is_container_side_condition, proof_encoding::ProofInstrumentor},
    util::{FreshGen, HashMap, HashSet, SymbolGen},
};

/// Holds all the names used in proof encoding.
/// We need fresh names that don't collide with user-defined names.
/// All of these names should be generated with the single global [`SymbolGen`].
#[derive(Clone)]
pub(crate) struct EncodingNames {
    pub(crate) proof_datatype: String,
    /// Prefix of the fiat justifications, which name their two endpoints by
    /// value: sort `S`'s constructor is [`Self::fiat`]. Derived from one name
    /// for the same reason as [`Self::rule_fused_prefix`].
    pub(crate) fiat_prefix: String,
    /// The sorts [`ProofInstrumentor::fiat_constructor`] has declared.
    pub(crate) fiat_declared: HashSet<String>,
    /// Prefix of the rule proofs carrying their body premises inline: premise
    /// count `k`'s constructor is [`Self::fused_rule`]. One prefix rather than a
    /// name per arity, so that re-parsing a desugared program recovers the same
    /// names without having encoded its rules.
    pub(crate) rule_fused_prefix: String,
    /// The premise counts [`ProofInstrumentor::rule_arity_header`] has declared.
    pub(crate) rule_fused_declared: HashSet<usize>,
    /// A later proof of the same head: the previous column's rule proof plus one
    /// canonicalization bridge.
    pub(crate) rule_link_constructor: String,
    /// Prefix of the packed proof constructors carrying a [`Skeleton`] and the
    /// columns it composes over: column count `k`'s constructor is
    /// [`Self::packed_proof`]. Derived from one name for the same reason as
    /// [`Self::rule_fused_prefix`].
    pub(crate) packed_prefix: String,
    /// The column counts [`ProofInstrumentor::packed_proof_constructor`] has
    /// declared.
    pub(crate) packed_declared: HashSet<usize>,
    pub(crate) merge_fn_idx_constructor: String,
    pub(crate) merge_fn_row_constructor: String,
    pub(crate) eq_trans_constructor: String,
    pub(crate) eq_sym_constructor: String,
    pub(crate) congr_constructor: String,
    pub(crate) congr_all_constructor: String,
    pub(crate) proj_constructor: String,
    /// Prefix of the element-matching projections, minted where the child's
    /// position in the term is only known once the term is in hand (see
    /// [`crate::proofs::proof_container_rebuild`]). The child is named by value,
    /// so sort `S`'s constructor is [`Self::proj_all`]. Derived from one name for
    /// the same reason as [`Self::rule_fused_prefix`].
    pub(crate) proj_all_prefix: String,
    /// The sorts [`ProofInstrumentor::proj_all_constructor`] has declared.
    pub(crate) proj_all_declared: HashSet<String>,
    pub(crate) container_normalize_constructor: String,
    pub(crate) eval_constructor: String,
    pub(crate) fn_to_term_sort: HashMap<String, String>,
    // Ruleset names
    pub(crate) path_compress_ruleset_name: String,
    pub(crate) rebuilding_ruleset_name: String,
    pub(crate) rebuilding_cleanup_ruleset_name: String,
    pub(crate) subsume_ruleset_name: String,
    // Per-function fresh names
    pub(crate) view_name: HashMap<String, String>,
    pub(crate) subsumed_name: HashMap<String, String>,
    /// The functions whose subsumption scaffolding some program has already
    /// declared (see [`ProofInstrumentor::subsume_marker`]).
    pub(crate) subsume_declared: HashSet<String>,
}

/// A proof composed out of the equality axioms over leaves of type `L`. Two
/// leaves are in use — a [`Composition`]'s and a [`Skeleton`]'s — and
/// [`Composition::pack`] is the map between them.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub(crate) enum ProofTree<L> {
    Leaf(L),
    Sym(Box<ProofTree<L>>),
    Trans(Box<ProofTree<L>>, Box<ProofTree<L>>),
    /// The child position the step rewrites.
    Congr(Box<ProofTree<L>>, usize, Box<ProofTree<L>>),
    /// The child position projected out of the inner proof's right-hand side.
    Proj(Box<ProofTree<L>>, usize),
}

/// The composition one packed proof row stands for, written over the row's own
/// proof columns: a leaf is the proof in a column. A column a composition
/// reaches twice is named twice and carried once; a column it does not reach is
/// carried and never read.
///
/// A packed row carries [`Skeleton::spelling`] in its first column, so the site
/// writing the row and the unpacking that reads it work from one statement of
/// the composition.
pub(crate) type Skeleton = ProofTree<usize>;

/// A composition the encoder has built but not written a row for. A leaf names
/// a proof variable already in scope; the whole tree becomes one row where
/// something reads it.
pub(crate) type Composition = ProofTree<String>;

impl<L> ProofTree<L> {
    pub(crate) fn sym(self) -> Self {
        ProofTree::Sym(Box::new(self))
    }

    pub(crate) fn trans(self, rhs: Self) -> Self {
        ProofTree::Trans(Box::new(self), Box::new(rhs))
    }

    /// This composition with one more congruence step, rewriting the child at
    /// position `child` by the proof `step` reaches.
    pub(crate) fn congr(self, child: usize, step: Self) -> Self {
        ProofTree::Congr(Box::new(self), child, Box::new(step))
    }

    /// The reflexive proof of this composition's child at position `child`.
    pub(crate) fn proj(self, child: usize) -> Self {
        ProofTree::Proj(Box::new(self), child)
    }

    /// The leaf this is, when it names one rather than composing.
    pub(crate) fn leaf(&self) -> Option<&L> {
        match self {
            ProofTree::Leaf(leaf) => Some(leaf),
            _ => None,
        }
    }
}

impl Skeleton {
    /// How many columns the row has.
    pub(crate) fn width(&self) -> usize {
        match self {
            ProofTree::Leaf(column) => column + 1,
            ProofTree::Sym(inner) | ProofTree::Proj(inner, _) => inner.width(),
            ProofTree::Trans(left, right) | ProofTree::Congr(left, _, right) => {
                left.width().max(right.width())
            }
        }
    }

    /// This skeleton with `column` read as the identity. `None` when that
    /// leaves nothing to state: the skeleton is that column, or every step it
    /// keeps rests on one that is — so a caller must not drop the column the
    /// whole composition stands on.
    ///
    /// The result proves what this skeleton does exactly when the column's
    /// proof is reflexive, which is the caller's to establish (see
    /// [`DropReflexiveStep`]). A projection is the one node whose conclusion is
    /// not its base's, so `None` under one would read as the identity while
    /// standing for the projected child: no skeleton may rest a projection on
    /// the dropped column alone.
    pub(crate) fn without_column(&self, column: usize) -> Option<Skeleton> {
        match self {
            ProofTree::Leaf(named) => (*named != column).then_some(ProofTree::Leaf(*named)),
            ProofTree::Sym(inner) => Some(inner.without_column(column)?.sym()),
            ProofTree::Trans(left, right) => {
                match (left.without_column(column), right.without_column(column)) {
                    (Some(left), Some(right)) => Some(left.trans(right)),
                    (left, right) => left.or(right),
                }
            }
            ProofTree::Congr(base, child, step) => match step.without_column(column) {
                Some(step) => {
                    let base = base.without_column(column);
                    debug_assert!(
                        base.is_some(),
                        "{self:?} rests its congruence base on column {column} alone while \
                         keeping the step, so dropping the column would lose the step's rewrite"
                    );
                    Some(base?.congr(*child, step))
                }
                None => base.without_column(column),
            },
            ProofTree::Proj(base, child) => {
                let base = base.without_column(column);
                debug_assert!(
                    base.is_some(),
                    "{self:?} rests its projection on column {column} alone, so dropping the \
                     column would read as the identity of the projected child"
                );
                Some(base?.proj(*child))
            }
        }
    }

    /// This skeleton as the string a packed row carries: its nodes in prefix
    /// order, one `_`-separated token each — `sym`, `trans`, `congr`, `proj`,
    /// `p<column>` for a column, and a bare number for a congruence's or
    /// projection's child position. Panics unless [`Self::from_spelling`] reads
    /// it back, since that is all unpacking has to go on.
    pub(crate) fn spelling(&self) -> String {
        let mut tokens = vec![];
        self.spell(&mut tokens);
        let spelling = tokens.join("_");
        assert_eq!(
            Skeleton::from_spelling(&spelling).as_ref(),
            Some(self),
            "{spelling} does not spell {self:?}"
        );
        spelling
    }

    fn spell(&self, tokens: &mut Vec<String>) {
        match self {
            ProofTree::Leaf(column) => tokens.push(format!("p{column}")),
            ProofTree::Sym(inner) => {
                tokens.push("sym".to_string());
                inner.spell(tokens);
            }
            ProofTree::Trans(left, right) => {
                tokens.push("trans".to_string());
                left.spell(tokens);
                right.spell(tokens);
            }
            ProofTree::Congr(base, child, step) => {
                tokens.push("congr".to_string());
                base.spell(tokens);
                tokens.push(child.to_string());
                step.spell(tokens);
            }
            ProofTree::Proj(base, child) => {
                tokens.push("proj".to_string());
                base.spell(tokens);
                tokens.push(child.to_string());
            }
        }
    }

    /// The skeleton [`Self::spelling`] writes as `spelling`, or `None` when the
    /// string is not one. A column may be named more than once, or not at all,
    /// so how many columns the row has is the reader's to check against
    /// [`Self::width`].
    pub(crate) fn from_spelling(spelling: &str) -> Option<Skeleton> {
        let mut tokens = spelling.split('_');
        let skeleton = Skeleton::read(&mut tokens)?;
        tokens.next().is_none().then_some(skeleton)
    }

    fn read<'a>(tokens: &mut impl Iterator<Item = &'a str>) -> Option<Skeleton> {
        match tokens.next()? {
            "sym" => Some(Skeleton::read(tokens)?.sym()),
            "trans" => {
                let left = Skeleton::read(tokens)?;
                Some(left.trans(Skeleton::read(tokens)?))
            }
            "congr" => {
                let base = Skeleton::read(tokens)?;
                let child = tokens.next()?.parse().ok()?;
                Some(base.congr(child, Skeleton::read(tokens)?))
            }
            "proj" => {
                let base = Skeleton::read(tokens)?;
                Some(base.proj(tokens.next()?.parse().ok()?))
            }
            token => Some(ProofTree::Leaf(token.strip_prefix('p')?.parse().ok()?)),
        }
    }
}

impl Composition {
    /// This composition as a packed row: the [`Skeleton`] it states and the proof
    /// variable in each of the row's columns, in first use order. Equal subtrees
    /// share their columns, so a step the composition reaches twice is carried
    /// once.
    pub(crate) fn pack(&self) -> (Skeleton, Vec<String>) {
        let mut columns = vec![];
        let skeleton = self.lay_out(&mut HashMap::default(), &mut columns);
        (skeleton, columns)
    }

    fn lay_out(
        &self,
        laid_out: &mut HashMap<Composition, Skeleton>,
        columns: &mut Vec<String>,
    ) -> Skeleton {
        if let Some(skeleton) = laid_out.get(self) {
            return skeleton.clone();
        }
        let skeleton = match self {
            ProofTree::Leaf(proof) => {
                columns.push(proof.clone());
                ProofTree::Leaf(columns.len() - 1)
            }
            ProofTree::Sym(inner) => inner.lay_out(laid_out, columns).sym(),
            ProofTree::Trans(left, right) => {
                let left = left.lay_out(laid_out, columns);
                left.trans(right.lay_out(laid_out, columns))
            }
            ProofTree::Congr(base, child, step) => {
                let base = base.lay_out(laid_out, columns);
                base.congr(*child, step.lay_out(laid_out, columns))
            }
            ProofTree::Proj(base, child) => base.lay_out(laid_out, columns).proj(*child),
        };
        laid_out.insert(self.clone(), skeleton.clone());
        skeleton
    }
}

/// Which proof of a rule head a row states: the column naming its position in
/// the head's flat array of proofs (see [`crate::proofs::proof_head`]), as an
/// `i64`-valued egglog expression.
#[derive(Clone)]
pub(crate) enum HeadColumn {
    Numbered(String),
    /// A rule row the walk gave no column: the placeholder before the encoder
    /// fills one in, and a position inside a head that concludes nothing. It
    /// renders as `-1`, which reading a proof back panics on.
    Unnumbered,
}

impl HeadColumn {
    /// The column value as an egglog expression.
    fn expr(&self) -> String {
        match self {
            HeadColumn::Numbered(expr) => expr.clone(),
            HeadColumn::Unnumbered => "-1".to_string(),
        }
    }
}

/// What justifies the proofs the encoder mints for an action. Which proof of the
/// head a mint states is left as a [`HeadColumn`], filled in once the encoder's
/// walk knows the column it is at. Internal to the encoder, not part of the proof
/// format.
#[derive(Clone)]
pub(crate) enum Justification {
    /// Rule-name expression, one premise-proof expression per body fact, and
    /// which of the head's proofs is being stated.
    Rule(String, Vec<String>, HeadColumn),
    Fiat,
    /// Term-free merge justification for a merge-body subexpression: function
    /// name, the two premise (view) proof expressions, and the pre-order index of
    /// this subexpression in the merge body (matches `subexpr_at_index` in proof
    /// conversion). It names no term, so it needs neither the merged term nor
    /// the function key/children — usable in a `:merge` action.
    MergeIdx(String, String, String, usize),
    /// Term-free merge justification for the whole view row (function name + two
    /// premise proof expressions). The conclusion `f(children, merged)` is
    /// reconstructed during proof conversion by running the whole merge body on
    /// the premise outputs, so the row names no term.
    MergeRow(String, String, String),
}

impl Justification {
    /// The same justification about `column`. Only a rule justification names a
    /// column; anything else is returned unchanged.
    pub(crate) fn at(&self, column: HeadColumn) -> Justification {
        match self {
            Justification::Rule(name, proofs, _) => {
                Justification::Rule(name.clone(), proofs.clone(), column)
            }
            other => other.clone(),
        }
    }

    /// The egglog expression for the `Rule` row's column.
    pub(crate) fn column_expr(&self) -> String {
        match self {
            Justification::Rule(_, _, column) => column.expr(),
            _ => HeadColumn::Unnumbered.expr(),
        }
    }
}

impl EncodingNames {
    /// The fiat justification whose two endpoints are values of `sort`.
    pub(crate) fn fiat(&self, sort: &str) -> String {
        format!("{}_{sort}", self.fiat_prefix)
    }

    /// Whether `head` is one of [`Self::fiat`]'s constructors.
    pub(crate) fn is_fiat(&self, head: &str) -> bool {
        head.strip_prefix(&self.fiat_prefix)
            .is_some_and(|sort| sort.starts_with('_'))
    }

    /// The element-matching projection naming a child of `sort`.
    pub(crate) fn proj_all(&self, sort: &str) -> String {
        format!("{}_{sort}", self.proj_all_prefix)
    }

    /// Whether `head` is one of [`Self::proj_all`]'s constructors.
    pub(crate) fn is_proj_all(&self, head: &str) -> bool {
        head.strip_prefix(&self.proj_all_prefix)
            .is_some_and(|sort| sort.starts_with('_'))
    }

    /// The rule proof constructor carrying `arity` premise proofs inline.
    pub(crate) fn fused_rule(&self, arity: usize) -> String {
        format!("{}_{arity}", self.rule_fused_prefix)
    }

    /// The premise count `head` carries inline, when it is one of
    /// [`Self::fused_rule`]'s constructors.
    pub(crate) fn fused_rule_arity(&self, head: &str) -> Option<usize> {
        head.strip_prefix(&self.rule_fused_prefix)?
            .strip_prefix('_')?
            .parse()
            .ok()
    }

    /// The packed proof constructor carrying a [`Skeleton`] over `columns` proof
    /// columns.
    pub(crate) fn packed_proof(&self, columns: usize) -> String {
        format!("{}_{columns}", self.packed_prefix)
    }

    /// The proof-column count `head` carries, when it is one of
    /// [`Self::packed_proof`]'s constructors.
    pub(crate) fn packed_proof_columns(&self, head: &str) -> Option<usize> {
        head.strip_prefix(&self.packed_prefix)?
            .strip_prefix('_')?
            .parse()
            .ok()
    }

    pub(crate) fn new(symbol_gen: &mut SymbolGen) -> Self {
        Self {
            proof_datatype: symbol_gen.fresh("Proof"),
            fiat_prefix: symbol_gen.fresh("Fiat"),
            fiat_declared: HashSet::default(),
            rule_fused_prefix: symbol_gen.fresh("Rule"),
            rule_fused_declared: HashSet::default(),
            rule_link_constructor: symbol_gen.fresh("RuleLink"),
            packed_prefix: symbol_gen.fresh("Packed"),
            packed_declared: HashSet::default(),
            merge_fn_idx_constructor: symbol_gen.fresh("MergeIdx"),
            merge_fn_row_constructor: symbol_gen.fresh("MergeRow"),
            eq_trans_constructor: symbol_gen.fresh("Trans"),
            eq_sym_constructor: symbol_gen.fresh("Sym"),
            congr_constructor: symbol_gen.fresh("Congr"),
            congr_all_constructor: symbol_gen.fresh("CongrAll"),
            proj_constructor: symbol_gen.fresh("Proj"),
            proj_all_prefix: symbol_gen.fresh("ProjAll"),
            proj_all_declared: HashSet::default(),
            container_normalize_constructor: symbol_gen.fresh("ContainerNormalize"),
            eval_constructor: symbol_gen.fresh("Eval"),
            fn_to_term_sort: HashMap::default(),
            path_compress_ruleset_name: symbol_gen.fresh("parent"),
            rebuilding_ruleset_name: symbol_gen.fresh("rebuilding"),
            rebuilding_cleanup_ruleset_name: symbol_gen.fresh("rebuilding_cleanup"),
            subsume_ruleset_name: symbol_gen.fresh("subsume_ruleset"),
            view_name: HashMap::default(),
            subsumed_name: HashMap::default(),
            subsume_declared: HashSet::default(),
        }
    }
}

impl ProofInstrumentor<'_> {
    pub(crate) fn uf_name(&mut self, sort: &str) -> String {
        if let Some(name) = self.egraph.proof_state.uf_parent.get(sort) {
            name.clone()
        } else {
            let fresh_name = self.egraph.parser.symbol_gen.fresh(&format!("UF_{sort}"));
            self.egraph
                .proof_state
                .uf_parent
                .insert(sort.to_string(), fresh_name.clone());
            fresh_name
        }
    }

    pub(crate) fn parse_program(&mut self, input: &str) -> Vec<Command> {
        self.egraph.parser.ensure_no_reserved_symbols = false;
        let res = self.egraph.parse_program_timed(None, input);
        self.egraph.parser.ensure_no_reserved_symbols = true;

        // This program is generated internally by term encoding, so a parse
        // failure is an egglog bug rather than a user error.
        res.expect("internally generated term-encoding program must parse")
    }

    /// Like [`Self::parse_program`], but groups each maximal run of consecutive
    /// top-level actions into one [`Command::Actions`] block. Non-action commands
    /// pass through in place, preserving order.
    pub(crate) fn parse_program_as_local_actions(&mut self, input: &str) -> Vec<Command> {
        use crate::ast::GenericActions;
        let mut out: Vec<Command> = vec![];
        let mut pending: Vec<crate::ast::Action> = vec![];
        let flush = |pending: &mut Vec<crate::ast::Action>, out: &mut Vec<Command>| {
            if !pending.is_empty() {
                out.push(Command::Actions(GenericActions::new(std::mem::take(
                    pending,
                ))));
            }
        };
        for command in self.parse_program(input) {
            match command {
                Command::Action(action) => pending.push(action),
                other => {
                    flush(&mut pending, &mut out);
                    out.push(other);
                }
            }
        }
        flush(&mut pending, &mut out);
        out
    }

    /// Declarations for the fused rule constructors `program`'s rules need but
    /// that no earlier program declared. A rule's premise count is fixed by its
    /// body (see [`recomputable_premises`]), so the arities a program uses are
    /// known before it is encoded; these are emitted ahead of the program's own
    /// commands.
    pub(crate) fn rule_arity_header(&mut self, program: &[ResolvedNCommand]) -> Vec<Command> {
        fn collect(commands: &[ResolvedNCommand], out: &mut Vec<usize>) {
            for command in commands {
                match command {
                    ResolvedNCommand::NormRule { rule } => out.push(
                        recomputable_premises(&rule.body, &|_| false)
                            .iter()
                            .filter(|recomputable| !**recomputable)
                            .count(),
                    ),
                    ResolvedNCommand::Fail(_, nested) => collect(nested, out),
                    _ => {}
                }
            }
        }
        let mut arities = vec![];
        collect(program, &mut arities);
        arities.sort_unstable();
        arities.dedup();

        let mut decls = vec![];
        for arity in arities {
            if !self
                .egraph
                .proof_state
                .proof_names
                .rule_fused_declared
                .insert(arity)
            {
                continue;
            }
            let names = self.proof_names();
            let name = names.fused_rule(arity);
            let proof = names.proof_datatype.clone();
            let premises = vec![proof.as_str(); arity].join(" ");
            let sep = if arity == 0 { "" } else { " " };
            decls.push(format!(
                "(function {name} (String{sep}{premises} i64 {proof}) Unit :no-merge :internal-hidden :internal-term-node)"
            ));
        }
        if decls.is_empty() {
            return vec![];
        }
        let decls = decls.join("\n");
        self.parse_program(&decls)
    }

    /// The packed proof constructor for a row of `columns` proof columns,
    /// together with its declaration — empty once some program has declared it.
    ///
    /// A row's column count is a property of the site packing it, not of the
    /// proof format, so the declaration is emitted with the first commands using
    /// it.
    pub(crate) fn packed_proof_constructor(&mut self, columns: usize) -> (String, String) {
        let name = self.proof_names().packed_proof(columns);
        if !self
            .egraph
            .proof_state
            .proof_names
            .packed_declared
            .insert(columns)
        {
            return (name, String::new());
        }
        let proof = self.proof_names().proof_datatype.clone();
        let columns: String = std::iter::repeat_n(format!("{proof} "), columns).collect();
        let decl = format!(
            "(function {name} (String {columns}{proof}) Unit :no-merge :internal-hidden :internal-term-node)\n"
        );
        (name, decl)
    }

    /// Header commands for term encoding, setting up rulesets.
    pub(crate) fn term_header(&mut self) -> Vec<Command> {
        let str = format!(
            "(ruleset {})
             (ruleset {})
             (ruleset {})
             (ruleset {})",
            self.proof_names().path_compress_ruleset_name,
            self.proof_names().rebuilding_ruleset_name,
            self.proof_names().rebuilding_cleanup_ruleset_name,
            self.proof_names().subsume_ruleset_name
        );
        self.parse_program(&str)
    }

    /// Internal parse helper for term encoding- parse and crash on failure.
    pub(crate) fn parse_schedule(&mut self, input: String) -> Schedule {
        self.egraph.parser.ensure_no_reserved_symbols = false;
        let res = self.egraph.parser.get_schedule_from_string(None, &input);
        self.egraph.parser.ensure_no_reserved_symbols = true;
        res.expect("internally generated term-encoding schedule must parse")
    }

    /// Internal parse helper for term encoding- parse and crash on failure.
    pub(crate) fn parse_facts(&mut self, input: &[String]) -> Vec<Fact> {
        self.egraph.parser.ensure_no_reserved_symbols = false;
        let res = input
            .iter()
            .map(|f| {
                self.egraph
                    .parser
                    .get_fact_from_string(None, f)
                    .expect("internally generated term-encoding fact must parse")
            })
            .collect();
        self.egraph.parser.ensure_no_reserved_symbols = true;
        res
    }

    /// Internal parse helper for term encoding- parse an expression and crash on failure.
    pub(crate) fn parse_expr(&mut self, input: &str) -> Expr {
        self.egraph.parser.ensure_no_reserved_symbols = false;
        let res = self.egraph.parser.get_expr_from_string(None, input);
        self.egraph.parser.ensure_no_reserved_symbols = true;
        res.expect("internally generated term-encoding expression must parse")
    }

    // Each function/constructor gets a view table, the canonicalized e-nodes to accelerate e-matching.
    pub(crate) fn view_name(&mut self, name: &str) -> String {
        if let Some(n) = self.egraph.proof_state.proof_names.view_name.get(name) {
            n.clone()
        } else {
            let fresh_name = self.egraph.parser.symbol_gen.fresh(&format!("{name}View"));
            self.egraph
                .proof_state
                .proof_names
                .view_name
                .insert(name.to_string(), fresh_name.clone());
            fresh_name
        }
    }

    pub(crate) fn subsumed_name(&mut self, name: &str) -> String {
        if let Some(n) = self.egraph.proof_state.proof_names.subsumed_name.get(name) {
            n.clone()
        } else {
            let fresh_name = self
                .egraph
                .parser
                .symbol_gen
                .fresh(&format!("to_subsume_{name}"));
            self.egraph
                .proof_state
                .proof_names
                .subsumed_name
                .insert(name.to_string(), fresh_name.clone());
            fresh_name
        }
    }

    pub(crate) fn proof_names(&self) -> &EncodingNames {
        &self.egraph.proof_state.proof_names
    }

    pub(crate) fn proofs_enabled(&self) -> bool {
        self.egraph.proof_state.proofs_enabled
    }

    /// The evaluation-mode option for a generated rule that reads the database
    /// in its action: `:unsafe-seminaive`, or `:naive` (the safe whole-database
    /// baseline) under the `force_proof_naive` test knob.
    pub(crate) fn rhs_read_eval_opt(&self) -> &'static str {
        if self.egraph.proof_state.force_proof_naive {
            ":naive"
        } else {
            ":unsafe-seminaive"
        }
    }

    /// Returns the proof output type: `Proof` when proofs are enabled, `Unit` otherwise.
    pub(crate) fn proof_type_str(&self) -> &str {
        if self.proofs_enabled() {
            &self.proof_names().proof_datatype
        } else {
            "Unit"
        }
    }

    /// A fresh name for an encoder temporary.
    pub(crate) fn fresh_var(&mut self) -> String {
        // Keep this hint distinct from the `"v"` that `proofs::proof_normal_form`
        // gives a rule's body variables. `SymbolGen` counts per hint, so sharing
        // one would number body variables by how many temporaries the encoder
        // happened to mint — and those names are printed in a proof's
        // `substitution`, so minting one more proof node would rewrite unrelated
        // proof output.
        self.egraph.parser.symbol_gen.fresh("pv")
    }

    /// Header string for proof encoding, defining sorts and constructors.
    /// Correspondings to `RawProof` in [`crate::proofs::proof_format`].
    pub(crate) fn proof_header(&mut self) -> String {
        let EncodingNames {
            ref proof_datatype,
            ref fiat_prefix,
            ref rule_link_constructor,
            ref merge_fn_idx_constructor,
            ref merge_fn_row_constructor,
            ref eq_trans_constructor,
            ref eq_sym_constructor,
            ref congr_constructor,
            ref congr_all_constructor,
            ref proj_constructor,
            ref proj_all_prefix,
            ref container_normalize_constructor,
            ref eval_constructor,
            ..
        } = *self.proof_names();

        format!(
            "
;; The proof datatype records the global proof constructor names so container
;; rebuild can recover them on re-parse (see ContainerRebuildSpec).
(sort {proof_datatype} :internal-proof-names {congr_constructor} {congr_all_constructor} {eq_trans_constructor} {eq_sym_constructor} {container_normalize_constructor} {fiat_prefix} {proj_constructor} {proj_all_prefix})

;; Proof terms are relations, not constructors: the encoding mints a fresh id
;; and asserts the row (both in one `mint-<Relation>!` call), so congruent
;; duplicates are kept (never merged away) rather than relying on native
;; congruence. The final column of each relation is the minted output id.

;; Fiat justification for globals and primitives, gives two terms t1 = t2 for the
;; proposition being justified. Its endpoints are values of one sort, so there is
;; a `Fiat_<Sort>` per fiat-ed sort, declared on first use (see
;; `ProofInstrumentor::fiat_constructor`):
;;   (Fiat_<Sort> <term> <term> <proof>)
;; A rule proof written before its head interns anything carries its premises
;; inline, in a `Rule_<k>` declared per premise count (see `rule_arity_header`):
;;   (Rule_<k> <rule name> <one proof per body fact> <column>)
;; Every rule proof after that names an earlier column's proof — which carries
;; the shared premises and the bridges recorded before it — plus the one *bridge*
;; premise recorded since: the view-row proof of the subterm the head interned,
;; saying which e-class it landed in. `<column>` says which proof of the head's
;; lowering this is (see `proof_head`); proof conversion derives the proposition
;; from it, so no term is stored. The rule name is not repeated either: it is
;; read off the `Rule_<k>` row ending the chain.
;;   (RuleLink <earlier column's proof> <bridge proof> <column>)
(function {rule_link_constructor} ({proof_datatype} {proof_datatype} i64 {proof_datatype}) Unit :no-merge :internal-hidden :internal-term-node)

;; A site with a fixed composition rather than a rule head — a top-level action,
;; a merge body, a view rebuild, a merge collision — writes one packed row
;; standing for the whole composition, in a `Packed_<k>` declared per proof-column
;; count (see `packed_proof_constructor`). The first column spells the composition
;; over the rest, in prefix order: `sym`, `trans`, `congr`, `p<n>` for the proof in
;; column n, and a bare number for a congruence's child position. So
;;   (Packed_2 \"trans_sym_p0_p1\" <hi proof> <lo proof>)
;; is the `@UF` edge a merge collision displaces, where both carried proofs share
;; their left-hand side, and
;;   (Packed_2 \"congr_p0_3_p1\" <row proof> <step proof>)
;; is a view rebuild that canonicalized child column 3.

;; term-free merge justification for an FD custom-function view subexpression:
;; name of function, two premise proofs, and the pre-order index of the merge-body
;; subexpression whose conclusion is reconstructed during proof conversion
(function {merge_fn_idx_constructor} (String {proof_datatype} {proof_datatype} i64 {proof_datatype}) Unit :no-merge :internal-hidden :internal-term-node)
;; term-free merge justification for an FD custom-function view row:
;; name of function and two premise proofs; the whole-row conclusion is
;; reconstructed during proof conversion by running the whole merge body
(function {merge_fn_row_constructor} (String {proof_datatype} {proof_datatype} {proof_datatype}) Unit :no-merge :internal-hidden :internal-term-node)

;; transitivity of equality proofs
(function {eq_trans_constructor} ({proof_datatype} {proof_datatype} {proof_datatype}) Unit :no-merge :internal-hidden :internal-term-node)

;; symmetry of equality proofs
(function {eq_sym_constructor} ({proof_datatype} {proof_datatype}) Unit :no-merge :internal-hidden :internal-term-node)
;; given a proof that t1 = f(..., ci, ...)
;; and the child index i of ci in the term f(..., ci, ...)
;; and a proof that ci = c2,
;; produces a justification that t1 = f(..., c2, ...)
(function {congr_constructor} ({proof_datatype} i64 {proof_datatype} {proof_datatype}) Unit :no-merge :internal-hidden :internal-term-node)

;; element-matching congruence (used by container rebuilds): given a proof that
;; t1 = c and a proof that a = b, produces a justification that t1 = c with
;; every child of c equal to a replaced by b.
(function {congr_all_constructor} ({proof_datatype} {proof_datatype} {proof_datatype}) Unit :no-merge :internal-hidden :internal-term-node)

;; given a proof that t1 = f(..., ci, ...) and the child index i,
;; produces a justification that ci = ci
(function {proj_constructor} ({proof_datatype} i64 {proof_datatype}) Unit :no-merge :internal-hidden :internal-term-node)

;; element-matching projection: given a proof that t1 = c and a term a that is a
;; child of c, produces a justification that a = a. Used where the child's
;; position is only known once the term is in hand. The child is named by value,
;; so there is a `ProjAll_<Sort>` per projected sort, declared with that sort (see
;; `ProofInstrumentor::proj_all_constructor`):
;;   (ProjAll_<Sort> <proof> <term> <proof>)

;; given a proof that t1 = c, where c is a container term, produces a proof that
;; t1 = normalize(c) (the container's canonicalization: sort/dedup for sets,
;; last-write-wins for maps, sort for multisets)
(function {container_normalize_constructor} ({proof_datatype} {proof_datatype}) Unit :no-merge :internal-hidden :internal-term-node)

;; marks the proof of a container side condition. Carries nothing: the side
;; condition is re-evaluated against the rule body when checked.
(function {eval_constructor} ({proof_datatype}) Unit :no-merge :internal-hidden :internal-term-node)
                "
        )
    }
}

/// Reads a file and checks that its commands support the proof encoding.
pub fn file_supports_proofs(path: &Path) -> bool {
    file_supports_proofs_with_egraph(path, EGraph::default())
}

/// Reads a file, resolves it with the provided e-graph, and checks that its
/// commands support the proof encoding.
pub fn file_supports_proofs_with_egraph(path: &Path, mut egraph: EGraph) -> bool {
    let contents = match std::fs::read_to_string(path) {
        Ok(contents) => contents,
        Err(_) => return false,
    };

    let canonical = match std::fs::canonicalize(path) {
        Ok(canonical) => canonical,
        Err(_) => return false,
    };

    let filename = canonical.to_string_lossy().into_owned();
    let desugared = match egraph.resolve_program(Some(filename.clone()), &contents) {
        Ok(commands) => commands,
        Err(_) => return false,
    };

    program_supports_proofs(&desugared, &egraph.type_info)
}

/// Reasons why a command doesn't support proof encoding
#[derive(Debug, Clone, thiserror::Error)]
pub enum ProofEncodingUnsupportedReason {
    #[error("primitive operation lacks a validator function")]
    PrimitiveWithoutValidator,
    #[error(
        "a declared index names a user function, which the term/proof encoding replaces with a view whose columns differ; the encoding does not yet rewrite index declarations"
    )]
    IndexDeclaration,
    #[error(
        "action contains a function lookup. Finding the output of a function is only supported in queries."
    )]
    FunctionLookupInAction,
    #[error(
        "a container constructed in the query (a container-producing primitive result) is used in the actions. A query-built container is a side condition with no carryable proof, so it cannot be carried into an action."
    )]
    ContainerCreatedInQueryUsedInAction,
    #[error(
        "a rule premise proves an equality about a container the query itself built (a container-producing primitive result), or about a value read out of one. No view row names that value, so the encoding has no row to project its reflexive proof out of; match the value with an atom instead."
    )]
    ContainerCreatedInQueryProvedAbout,
    #[error(
        "a rule premise proves an equality about an eq-sort value a primitive computed without being handed a container to read it out of. No view row names that value, so the encoding has no row to project its reflexive proof out of; match the value with an atom instead."
    )]
    EqSortPrimitiveResultWithoutContainer,
    #[error(
        "sort has a presort (custom sort container implementation). Custom sorts are not supported by proof encoding."
    )]
    SortWithPresort,
    #[error(
        "sort has a :internal-uf annotation. The :internal-uf annotation is used internally by term encoding and cannot be specified manually in proof mode."
    )]
    SortWithUfAnnotation,
    #[error("user-defined commands are not supported.")]
    UserDefinedCommand,
    #[error("`fail` wrapping an `input` command is not supported by proof encoding.")]
    FailInputCommand,
    #[error(
        "let binding with a primitive in the body. For silly internal reasons, we don't support primitive bindings for proofs at the moment, sorry."
    )]
    LetBindingWithNonEqSort,
    #[error(
        "rule uses `:unsafe-seminaive`. Arbitrary RHS database reads are not representable by the term/proof encoding."
    )]
    UnsafeSeminaive,
    #[error(
        "rule uses `:naive` with an eq-sort primitive in the body. Proof encoding can only look up proofs for primitive eq-sort fact results under seminaive-safe query evaluation."
    )]
    NaiveEqSortPrimitiveFact,
    #[error("tuple-output functions are not supported by the term/proof encoding.")]
    TupleOutputFunction,
    #[error(
        "a user-written `begin` block (or `(let <var> (begin ...))`) is not supported by the term/proof encoding, which models top-level actions individually. Write the actions at the top level instead."
    )]
    UserWrittenBeginBlock,
    #[error(
        "a `:merge` action block (actions before the result value) is not supported by the term/proof encoding."
    )]
    MergeActionBlock,
    #[error(
        "eq-sort-output `:no-merge` functions are not supported by the term/proof encoding (their conflict check needs union-find leaders); run without term/proof encoding, or give the function a `:merge` (e.g. `:merge old`). Primitive/`Unit`-output `:no-merge` functions are supported."
    )]
    NoMergeEqSortFunction,
}

/// Checks whether a desugared program supports proof encoding.
pub fn program_supports_proofs(commands: &[ResolvedCommand], type_info: &TypeInfo) -> bool {
    // Globals defined anywhere in the program, including inside `(push)`/`(pop)`
    // scopes. `type_info.global_sorts` reflects only the final scope (each `pop`
    // unregisters its globals), so checking against it alone misreads a popped
    // global's action-side lookup as an unsupported function lookup.
    let let_globals: HashSet<String> = commands
        .iter()
        .filter_map(|c| match c {
            GenericCommand::Function {
                name,
                let_binding: true,
                ..
            } => Some(name.clone()),
            _ => None,
        })
        .collect();
    for command in commands {
        if let Err(reason) = command_supports_proof_encoding_impl(command, type_info, &let_globals)
        {
            let cmd = command.to_string();
            log::debug!(
                "program does not support proofs: {reason}\n  command: {}",
                &cmd[..cmd.len().min(160)]
            );
            return false;
        }
    }
    true
}

/// Recursively check if all primitives in an expression have validators
fn expr_primitives_have_validators(expr: &ResolvedExpr) -> bool {
    use crate::ast::GenericExpr;
    use crate::core::ResolvedCall;

    let mut all_valid = true;
    expr.walk(
        &mut |e| {
            if let GenericExpr::Call(_, ResolvedCall::Primitive(prim), _) = e
                && prim.validator().is_none()
            {
                all_valid = false;
            }
        },
        &mut |_| {},
    );
    all_valid
}

/// Check if an action contains non-global function lookups in any of its expressions
fn action_has_function_lookup(
    action: &ResolvedAction,
    type_info: &TypeInfo,
    extra_globals: &HashSet<String>,
) -> bool {
    let mut has_lookup = false;
    action.clone().visit_exprs(&mut |expr| {
        if expr_has_non_global_lookup(&expr, type_info, extra_globals) {
            has_lookup = true;
        }
        expr
    });
    has_lookup
}

/// Like [`TypeInfo::expr_has_function_lookup`], but also treating names in
/// `extra_globals` as globals (see [`program_supports_proofs`]).
fn expr_has_non_global_lookup(
    expr: &ResolvedExpr,
    type_info: &TypeInfo,
    extra_globals: &HashSet<String>,
) -> bool {
    use crate::ast::GenericExpr;
    expr.find(&mut |e| {
        if let GenericExpr::Call(span, ResolvedCall::Func(func_type), _) = e
            && func_type.subtype == crate::ast::FunctionSubtype::Custom
            && !type_info.is_global(&func_type.name)
            && !extra_globals.contains(&func_type.name)
        {
            return Some(span.clone());
        }
        None
    })
    .is_some()
}

/// Whether a fact contains a primitive call whose result is an eq-sort or
/// container value.
fn fact_has_eq_sort_primitive_result(fact: &ResolvedFact) -> bool {
    let mut has_eq_sort_primitive = false;
    fact.clone().visit_exprs(&mut |expr| {
        if let ResolvedExpr::Call(_, ResolvedCall::Primitive(prim), _) = &expr
            && (prim.output().is_eq_sort() || prim.output().is_eq_container_sort())
        {
            has_eq_sort_primitive = true;
        }
        expr
    });
    has_eq_sort_primitive
}

/// Whether `expr`'s premise proof is a reflexive fiat over a base value: a
/// literal, a base-sorted variable, or a base-output primitive over those.
/// `is_global` marks a variable naming a global, whose value no gated fact may
/// depend on (see [`recomputable_premises`]).
fn is_base_value_expr(expr: &ResolvedExpr, is_global: &dyn Fn(&str) -> bool) -> bool {
    let is_base = |sort: &ArcSort| !sort.is_eq_sort() && !sort.is_eq_container_sort();
    match expr {
        ResolvedExpr::Lit(..) => true,
        ResolvedExpr::Var(_, var) => is_base(&var.sort) && !is_global(&var.name),
        ResolvedExpr::Call(_, ResolvedCall::Primitive(prim), args) => {
            is_base(prim.output()) && args.iter().all(|arg| is_base_value_expr(arg, is_global))
        }
        ResolvedExpr::Call(..) => false,
    }
}

/// Whether every variable `expr` reads is in `bound`.
fn reads_only(expr: &ResolvedExpr, bound: &HashSet<String>) -> bool {
    match expr {
        ResolvedExpr::Lit(..) => true,
        ResolvedExpr::Var(_, var) => bound.contains(&var.name),
        ResolvedExpr::Call(_, _, args) => args.iter().all(|arg| reads_only(arg, bound)),
    }
}

/// Record every variable `expr` mentions as bound.
fn bind_vars(expr: &ResolvedExpr, bound: &mut HashSet<String>) {
    match expr {
        ResolvedExpr::Lit(..) => {}
        ResolvedExpr::Var(_, var) => {
            bound.insert(var.name.clone());
        }
        ResolvedExpr::Call(_, _, args) => args.iter().for_each(|arg| bind_vars(arg, bound)),
    }
}

/// Which of a rule body's facts the encoding stores no premise proof for: the
/// premise is a reflexive fiat over a base value, which proof conversion
/// recomputes by evaluating the fact against the bindings the earlier facts
/// give. Answered per fact, in body order, since a fact is only recomputable
/// once one of its sides reads nothing but variables the body has already bound.
///
/// The encoder and proof conversion share this gate so they cannot drift, and
/// each must therefore describe the same rule the same way. `remove_globals`
/// rewrites a global reference into a lookup call, which is not a base value, so
/// conversion — which sees the rule from before that pass — reports a global's
/// variable through `is_global` to reach the same answer.
pub(crate) fn recomputable_premises(
    body: &[ResolvedFact],
    is_global: &dyn Fn(&str) -> bool,
) -> Vec<bool> {
    let mut bound: HashSet<String> = HashSet::default();
    let mut out = Vec::with_capacity(body.len());
    for fact in body {
        // A side is usable when it evaluates here, or is the bare variable
        // unification binds from the proposition.
        let usable = |expr: &ResolvedExpr, bound: &HashSet<String>| {
            reads_only(expr, bound) || matches!(expr, ResolvedExpr::Var(..))
        };
        let recomputable = !is_container_side_condition(fact)
            && match fact {
                ResolvedFact::Fact(expr) => {
                    is_base_value_expr(expr, is_global) && reads_only(expr, &bound)
                }
                ResolvedFact::Eq(_, lhs, rhs) => {
                    is_base_value_expr(lhs, is_global)
                        && is_base_value_expr(rhs, is_global)
                        && usable(lhs, &bound)
                        && usable(rhs, &bound)
                        && (reads_only(lhs, &bound) || reads_only(rhs, &bound))
                }
            };
        out.push(recomputable);
        match fact {
            ResolvedFact::Fact(expr) => bind_vars(expr, &mut bound),
            ResolvedFact::Eq(_, lhs, rhs) => {
                bind_vars(lhs, &mut bound);
                bind_vars(rhs, &mut bound);
            }
        }
    }
    out
}

/// Whether `sort` is a container that can hold an element of `element`.
pub(super) fn holds_sort(sort: &ArcSort, element: &str) -> bool {
    sort.is_eq_container_sort()
        && sort
            .inner_sorts()
            .iter()
            .any(|inner| inner.name() == element || holds_sort(inner, element))
}

/// Whether `expr` is a container-producing primitive call — the query computing
/// a container rather than reading one out of the database.
fn builds_a_container(expr: &ResolvedExpr) -> bool {
    matches!(
        expr,
        ResolvedExpr::Call(_, ResolvedCall::Primitive(prim), _)
            if prim.output().is_eq_container_sort()
    )
}

/// The variables a rule body binds to a container the query builds.
fn query_built_containers(body: &[ResolvedFact]) -> Vec<String> {
    let mut built = Vec::new();
    for fact in body {
        if let ResolvedFact::Eq(_, lhs, rhs) = fact {
            for (var_side, call_side) in [(lhs, rhs), (rhs, lhs)] {
                if let ResolvedExpr::Var(_, v) = var_side
                    && builds_a_container(call_side)
                {
                    built.push(v.name.clone());
                }
            }
        }
    }
    built
}

/// One value a rule body binds: a variable, or one occurrence of a call the
/// query evaluates. Two occurrences of the same call are two values, as they
/// are to the encoder.
#[derive(Clone, PartialEq, Eq, Hash)]
enum BodyValue {
    Var(String),
    Call(usize),
}

/// What one body expression contributes to a [`BodyAnchorScan`].
struct Scanned {
    /// The value the expression denotes.
    value: BodyValue,
    /// Whether its proof proves `t = t`.
    reflexive: bool,
    /// When that proof is a reflexive anchor, the reason to report if the body
    /// turns out to supply none.
    anchor: Option<ProofEncodingUnsupportedReason>,
}

/// The reflexive anchors a rule body offers and the ones its premises read, as
/// the encoder collects them (see
/// [`crate::proofs::proof_encoding::BodyAnchors`]).
#[derive(Default)]
struct BodyAnchorScan {
    /// Values a view atom's row proof reaches.
    rows: HashSet<BodyValue>,
    /// Values the body's equalities force equal, so either one's anchor serves
    /// both.
    aliases: Vec<(BodyValue, BodyValue)>,
    /// A value a primitive read out of a container, and the arguments it could
    /// have come out of.
    elements: HashMap<BodyValue, Vec<BodyValue>>,
    /// The anchors the body's premises read, with [`Scanned::anchor`]'s reason.
    requests: Vec<(BodyValue, ProofEncodingUnsupportedReason)>,
    /// Calls scanned so far, numbering [`BodyValue::Call`].
    calls: usize,
}

impl BodyAnchorScan {
    fn scan(body: &[ResolvedFact]) -> Self {
        let mut scan = Self::default();
        for fact in body {
            scan.fact(fact);
        }
        scan
    }

    fn fresh(&mut self) -> BodyValue {
        self.calls += 1;
        BodyValue::Call(self.calls)
    }

    fn fact(&mut self, fact: &ResolvedFact) {
        // A container side condition's premise is the `Eval` marker, which
        // reads no anchor.
        if is_container_side_condition(fact) {
            return;
        }
        match fact {
            // A custom function's view atom: its row proof is reflexive over the
            // whole application, so it reaches the arguments and the output.
            ResolvedFact::Eq(
                _,
                ResolvedExpr::Call(_, ResolvedCall::Func(func_type), args),
                ResolvedExpr::Var(_, out),
            ) if func_type.subtype == crate::ast::FunctionSubtype::Custom => {
                for arg in args {
                    let scanned = self.expr(arg);
                    self.rows.insert(scanned.value);
                }
                self.rows.insert(BodyValue::Var(out.name.clone()));
            }
            ResolvedFact::Eq(_, lhs, rhs) => {
                let (lhs, rhs) = (self.expr(lhs), self.expr(rhs));
                self.aliases.push((lhs.value, rhs.value.clone()));
                // The premise composes `Sym(left)` with `right` and drops
                // whichever side is reflexive, so the right-hand anchor is read
                // exactly when the left-hand proof is itself reflexive.
                if lhs.reflexive
                    && let Some(reason) = rhs.anchor
                {
                    self.requests.push((rhs.value, reason));
                }
            }
            // A guard's premise *is* its expression's proof: there is no second
            // side for the composition to drop it against, so the anchor is read
            // whenever the expression has one.
            ResolvedFact::Fact(expr) => {
                let scanned = self.expr(expr);
                if let Some(reason) = scanned.anchor {
                    self.requests.push((scanned.value, reason));
                }
            }
        }
    }

    fn expr(&mut self, expr: &ResolvedExpr) -> Scanned {
        match expr {
            // A literal is proved by a reflexive `Fiat`, which needs no anchor.
            ResolvedExpr::Lit(..) => Scanned {
                value: self.fresh(),
                reflexive: true,
                anchor: None,
            },
            // `remove_globals` reads a global reference off its FD view, whose
            // row proof reaches the value.
            ResolvedExpr::Var(_, var) if var.is_global_ref => {
                let value = BodyValue::Var(var.name.clone());
                self.rows.insert(value.clone());
                Scanned {
                    value,
                    reflexive: false,
                    anchor: None,
                }
            }
            ResolvedExpr::Var(_, var) => Scanned {
                value: BodyValue::Var(var.name.clone()),
                reflexive: true,
                anchor: if var.sort.is_eq_container_sort() {
                    Some(ProofEncodingUnsupportedReason::ContainerCreatedInQueryProvedAbout)
                } else if var.sort.is_eq_sort() {
                    Some(ProofEncodingUnsupportedReason::EqSortPrimitiveResultWithoutContainer)
                } else {
                    None
                },
            },
            ResolvedExpr::Call(_, call, args) => {
                let args: Vec<Scanned> = args.iter().map(|arg| self.expr(arg)).collect();
                let value = self.fresh();
                match call {
                    // A view atom: its row proof reads `eclass = f(children)`,
                    // reaching the call's own value and every argument.
                    ResolvedCall::Func(_) => {
                        self.rows.insert(value.clone());
                        self.rows.extend(args.into_iter().map(|arg| arg.value));
                        Scanned {
                            value,
                            reflexive: false,
                            anchor: None,
                        }
                    }
                    ResolvedCall::Primitive(prim) if prim.output().is_eq_container_sort() => {
                        Scanned {
                            value,
                            reflexive: false,
                            anchor: None,
                        }
                    }
                    // An eq-sort result is an element the primitive read out of
                    // whichever arguments can hold its sort.
                    ResolvedCall::Primitive(prim) if prim.output().is_eq_sort() => {
                        let containers: Vec<BodyValue> = prim
                            .input()
                            .iter()
                            .zip(&args)
                            .filter(|(sort, _)| holds_sort(sort, prim.output().name()))
                            .map(|(_, arg)| arg.value.clone())
                            .collect();
                        let anchor = if containers.is_empty() {
                            ProofEncodingUnsupportedReason::EqSortPrimitiveResultWithoutContainer
                        } else {
                            ProofEncodingUnsupportedReason::ContainerCreatedInQueryProvedAbout
                        };
                        self.elements.insert(value.clone(), containers);
                        Scanned {
                            value,
                            reflexive: true,
                            anchor: Some(anchor),
                        }
                    }
                    // A base result is a literal, proved by a reflexive `Fiat`.
                    ResolvedCall::Primitive(_) => Scanned {
                        value,
                        reflexive: true,
                        anchor: None,
                    },
                    ResolvedCall::Values(_) => Scanned {
                        value,
                        reflexive: false,
                        anchor: None,
                    },
                }
            }
        }
    }

    /// Every value the body's equalities relate to `value`, itself included.
    fn alias_class(&self, value: &BodyValue) -> HashSet<BodyValue> {
        let mut class: HashSet<BodyValue> = HashSet::default();
        let mut frontier = vec![value.clone()];
        while let Some(value) = frontier.pop() {
            if !class.insert(value.clone()) {
                continue;
            }
            for (left, right) in &self.aliases {
                if *left == value {
                    frontier.push(right.clone());
                } else if *right == value {
                    frontier.push(left.clone());
                }
            }
        }
        class
    }

    /// Whether an anchor for `value` can be projected out of a view row the body
    /// reads: one naming it, or one naming a container it was read out of.
    ///
    /// The encoder resolves an alias class to a single source and picks among
    /// several container reads arbitrarily, so a class of reads counts as
    /// anchored only when every read in it is.
    fn anchored(&self, value: &BodyValue, visiting: &mut HashSet<BodyValue>) -> bool {
        if !visiting.insert(value.clone()) {
            return false;
        }
        let class = self.alias_class(value);
        let reads: Vec<&Vec<BodyValue>> =
            class.iter().filter_map(|v| self.elements.get(v)).collect();
        let anchored = class.iter().any(|v| self.rows.contains(v))
            || (!reads.is_empty()
                && reads.iter().all(|containers| {
                    containers
                        .iter()
                        .any(|container| self.anchored(container, visiting))
                }));
        visiting.remove(value);
        anchored
    }
}

/// Why the encoding cannot prove a rule's body, if it cannot: a premise reads
/// the reflexive anchor of a value the query computed, which no view row names.
fn body_premise_without_anchor(body: &[ResolvedFact]) -> Option<ProofEncodingUnsupportedReason> {
    let scan = BodyAnchorScan::scan(body);
    scan.requests
        .iter()
        .find(|(value, _)| !scan.anchored(value, &mut HashSet::default()))
        .map(|(_, reason)| reason.clone())
}

/// Checks whether a resolved command supports proof encoding.
/// Returns Ok(()) if supported, or Err with the reason if not.
pub(crate) fn command_supports_proof_encoding(
    command: &ResolvedCommand,
    type_info: &TypeInfo,
) -> Result<(), ProofEncodingUnsupportedReason> {
    command_supports_proof_encoding_impl(command, type_info, &HashSet::default())
}

/// [`command_supports_proof_encoding`] with `extra_globals`: let-bound names
/// treated as globals even when out of scope in `type_info` (see
/// [`program_supports_proofs`]).
fn command_supports_proof_encoding_impl(
    command: &ResolvedCommand,
    type_info: &TypeInfo,
    extra_globals: &HashSet<String>,
) -> Result<(), ProofEncodingUnsupportedReason> {
    // `:unsafe-seminaive` rules perform arbitrary reads against the live
    // database; the term/proof encoding can't represent that.
    if let crate::ast::GenericCommand::Rule { rule } = command
        && rule.eval_mode == crate::ast::RuleEvalMode::UnsafeSeminaive
    {
        return Err(ProofEncodingUnsupportedReason::UnsafeSeminaive);
    }
    if let crate::ast::GenericCommand::Rule { rule } = command
        && rule.eval_mode == crate::ast::RuleEvalMode::Naive
        && rule.body.iter().any(fact_has_eq_sort_primitive_result)
    {
        return Err(ProofEncodingUnsupportedReason::NaiveEqSortPrimitiveFact);
    }
    // A declared index refers to a function's columns by position. The encoding
    // rewrites that function into a view with a different shape, so the
    // declaration would silently point at the wrong columns.
    if matches!(command, crate::ast::GenericCommand::Index { .. }) {
        return Err(ProofEncodingUnsupportedReason::IndexDeclaration);
    }
    // Tuple-output functions store multiple value columns, which the term/proof encoding (built
    // around single-output constructor views) does not model.
    if let crate::ast::GenericCommand::Function { schema, .. } = command
        && schema.is_tuple_output()
    {
        return Err(ProofEncodingUnsupportedReason::TupleOutputFunction);
    }

    // A user-written `begin` block keeps its bindings local, but proof checking
    // models top-level actions one at a time, so those locals have no checkable
    // representation. The encoding's own generated blocks are unaffected: they are
    // produced after this check, and proof checking runs against the pre-encoding
    // program.
    if matches!(
        command,
        crate::ast::GenericCommand::Actions(..) | crate::ast::GenericCommand::LetBegin(..)
    ) {
        return Err(ProofEncodingUnsupportedReason::UserWrittenBeginBlock);
    }

    // The conflict check for an eq-sort output needs union-find leaders (raw id
    // equality is not e-class equality), which the encoding has no eager hook for;
    // a file using one runs plain only. Primitive/`Unit`-output `:no-merge` is
    // supported (raw equality is equality there — encoded as an FD view declared
    // native `:no-merge` + `:internal-identity-vals 1`). Constructors/relations are
    // `Constructor` commands (not `Function`), and encoded globals (`:internal-let`,
    // produced by `remove_globals` before this check in the plain-resolve path
    // `file_supports_proofs` uses) have their own FD-view encoding — both excluded.
    if let crate::ast::GenericCommand::Function {
        merge: None,
        let_binding: false,
        schema,
        ..
    } = command
        && type_info
            .get_sort_by_name(schema.output())
            .is_some_and(|sort| sort.is_eq_sort())
    {
        return Err(ProofEncodingUnsupportedReason::NoMergeEqSortFunction);
    }

    // A `:merge` action block runs actions before its result; the proof encoding only instruments
    // the merged value, so mark it unsupported rather than emit silently-incomplete proofs.
    if let crate::ast::GenericCommand::Function {
        merge: Some(merge), ..
    } = command
        && !merge.actions.is_empty()
    {
        return Err(ProofEncodingUnsupportedReason::MergeActionBlock);
    }
    // Check all expressions for primitives without validators
    let mut all_primitives_have_validators = true;
    command.clone().visit_exprs(&mut |expr| {
        if !expr_primitives_have_validators(&expr) {
            all_primitives_have_validators = false;
        }
        expr
    });

    if !all_primitives_have_validators {
        return Err(ProofEncodingUnsupportedReason::PrimitiveWithoutValidator);
    }

    // Check actions (not queries) for function lookups
    // Egglog supports lookups in actions at the global level, but not in proofs mode
    // (global function calls are allowed - they get desugared to constructors)
    let mut has_function_lookup_in_action = false;
    command.clone().visit_actions(&mut |action| {
        has_function_lookup_in_action |=
            action_has_function_lookup(&action, type_info, extra_globals);
        action
    });

    if has_function_lookup_in_action {
        return Err(ProofEncodingUnsupportedReason::FunctionLookupInAction);
    }
    if let GenericCommand::Function {
        merge: Some(merge), ..
    } = command
        && expr_has_non_global_lookup(&merge.result, type_info, extra_globals)
    {
        return Err(ProofEncodingUnsupportedReason::FunctionLookupInAction);
    }

    // A value the query computes is anchored by projecting it out of a view row
    // the body reads, and a container a body primitive built is named by no such
    // row.
    if let GenericCommand::Rule { rule } = command {
        let constructed = query_built_containers(&rule.body);
        if !constructed.is_empty() {
            let mut used_in_action = false;
            for action in &rule.head.0 {
                action.clone().visit_exprs(&mut |expr| {
                    expr.walk(
                        &mut |e| {
                            if let ResolvedExpr::Var(_, v) = e
                                && constructed.contains(&v.name)
                            {
                                used_in_action = true;
                            }
                        },
                        &mut |_| {},
                    );
                    expr
                });
            }
            if used_in_action {
                return Err(ProofEncodingUnsupportedReason::ContainerCreatedInQueryUsedInAction);
            }
        }
        if let Some(reason) = body_premise_without_anchor(&rule.body) {
            return Err(reason);
        }
    }

    // Now check command-specific constraints
    match command {
        GenericCommand::Sort {
            name,
            presort_and_args: Some(_),
            ..
        } => type_info
            .get_sort_by_name(name)
            .filter(|sort| sort.is_container_sort())
            .map(|_| ())
            .ok_or(ProofEncodingUnsupportedReason::SortWithPresort),
        GenericCommand::Sort { uf: Some(_), .. } => {
            Err(ProofEncodingUnsupportedReason::SortWithUfAnnotation)
        }
        GenericCommand::UserDefined(..) => Err(ProofEncodingUnsupportedReason::UserDefinedCommand),
        // Extract commands can't have non-global function lookups
        // because instrument_action_expr doesn't support them
        // (global function calls are fine - they get desugared to constructors)
        GenericCommand::Extract(_, expr, variants) => {
            if expr_has_non_global_lookup(expr, type_info, extra_globals)
                || expr_has_non_global_lookup(variants, type_info, extra_globals)
            {
                Err(ProofEncodingUnsupportedReason::FunctionLookupInAction)
            } else {
                Ok(())
            }
        }
        GenericCommand::Fail(_, commands) => {
            for command in commands {
                if let GenericCommand::Input { .. } = command {
                    return Err(ProofEncodingUnsupportedReason::FailInputCommand);
                }
                command_supports_proof_encoding(command, type_info)?;
            }
            Ok(())
        }
        // let binding with non-eq sort not supported by proof_global_desugar
        ResolvedCommand::Action(ResolvedAction::Let(_, _, expr)) => {
            // let binding with non-eq sort not supported by proof_global_desugar
            // we detect as setting something that is no-merge to a primitive not supported (global primitive binding)
            if expr.output_type().is_eq_sort() {
                Ok(())
            } else {
                Err(ProofEncodingUnsupportedReason::LetBindingWithNonEqSort)
            }
        }
        // After global desugar it may look like this
        ResolvedCommand::Action(ResolvedAction::Set(_span, head, _children, expr)) => {
            if !type_info.is_global(head.name()) || expr.output_type().is_eq_sort() {
                Ok(())
            } else {
                Err(ProofEncodingUnsupportedReason::LetBindingWithNonEqSort)
            }
        }
        _ => Ok(()),
    }
}

/// The `proof-of-min` / `proof-of-max` primitives: given two `(value, proof)`
/// pairs `(a, ap)` and `(b, bp)`, return the proof paired with the smaller /
/// larger value (same value ordering as `ordering-min`/`ordering-max`; a tie
/// takes `bp`, matching those primitives keeping `b`). Typed
/// `(T, P, T, P) -> P` for any sorts `T` and `P`, so the encoding's generated
/// `:merge` blocks can pass sort values alongside their proofs.
#[derive(Clone)]
pub(crate) struct OrientProof {
    name: String,
    take_min: bool,
}

impl OrientProof {
    pub(crate) fn min() -> Self {
        Self {
            name: "proof-of-min".into(),
            take_min: true,
        }
    }

    pub(crate) fn max() -> Self {
        Self {
            name: "proof-of-max".into(),
            take_min: false,
        }
    }
}

impl crate::Primitive for OrientProof {
    fn name(&self) -> &str {
        &self.name
    }

    fn get_type_constraints(&self, span: &Span) -> Box<dyn crate::constraint::TypeConstraint> {
        Box::new(OrientProofTypeConstraint {
            name: self.name.clone(),
            span: span.clone(),
        })
    }
}

impl crate::PurePrim for OrientProof {
    fn apply<'a, 'db>(&self, _state: crate::PureState<'a, 'db>, args: &[Value]) -> Option<Value> {
        let [a, ap, b, bp] = args else {
            return None;
        };
        let first = if self.take_min { a < b } else { a > b };
        Some(if first { *ap } else { *bp })
    }
}

struct OrientProofTypeConstraint {
    name: String,
    span: Span,
}

impl crate::constraint::TypeConstraint for OrientProofTypeConstraint {
    fn get(
        &self,
        arguments: &[crate::core::AtomTerm],
        _typeinfo: &TypeInfo,
    ) -> Vec<Box<dyn crate::constraint::Constraint<crate::core::AtomTerm, crate::ArcSort>>> {
        // `(a ap b bp) -> out`: `a`/`b` share one sort; `ap`/`bp`/`out` another.
        if arguments.len() != 5 {
            return vec![crate::constraint::impossible(
                crate::constraint::ImpossibleConstraint::ArityMismatch {
                    atom: crate::core::Atom {
                        span: self.span.clone(),
                        head: self.name.clone(),
                        args: arguments.to_vec(),
                    },
                    expected: 5,
                },
            )];
        }
        vec![
            crate::constraint::eq(arguments[2].clone(), arguments[0].clone()),
            crate::constraint::eq(arguments[3].clone(), arguments[1].clone()),
            crate::constraint::eq(arguments[4].clone(), arguments[1].clone()),
        ]
    }
}

/// The `select-eq` primitive: `(select-eq test cand if-eq else) -> if-eq` when
/// `test == cand`, else `else`. Typed `(T T P P) -> P` for any sorts `T` and `P`.
///
/// Used by a custom function's FD-view `:merge` to keep its proof column stable:
/// when the merged output equals a colliding premise's output, reuse that
/// premise's existing proof rather than mint a fresh one. Without this the proof
/// column would change on every idempotent merge (`min`/`max`/...), bumping the
/// row's timestamp and preventing saturation.
#[derive(Clone)]
pub(crate) struct SelectEqProof;

impl crate::Primitive for SelectEqProof {
    fn name(&self) -> &str {
        "select-eq"
    }

    fn get_type_constraints(&self, span: &Span) -> Box<dyn crate::constraint::TypeConstraint> {
        Box::new(SelectEqProofTypeConstraint { span: span.clone() })
    }
}

impl crate::PurePrim for SelectEqProof {
    fn apply<'a, 'db>(&self, _state: crate::PureState<'a, 'db>, args: &[Value]) -> Option<Value> {
        let [test, cand, if_eq, els] = args else {
            return None;
        };
        Some(if test == cand { *if_eq } else { *els })
    }
}

struct SelectEqProofTypeConstraint {
    span: Span,
}

impl crate::constraint::TypeConstraint for SelectEqProofTypeConstraint {
    fn get(
        &self,
        arguments: &[crate::core::AtomTerm],
        _typeinfo: &TypeInfo,
    ) -> Vec<Box<dyn crate::constraint::Constraint<crate::core::AtomTerm, crate::ArcSort>>> {
        // `(test cand if-eq else) -> out`: `test`/`cand` share one sort;
        // `if-eq`/`else`/`out` another.
        if arguments.len() != 5 {
            return vec![crate::constraint::impossible(
                crate::constraint::ImpossibleConstraint::ArityMismatch {
                    atom: crate::core::Atom {
                        span: self.span.clone(),
                        head: "select-eq".to_string(),
                        args: arguments.to_vec(),
                    },
                    expected: 5,
                },
            )];
        }
        vec![
            crate::constraint::eq(arguments[1].clone(), arguments[0].clone()),
            crate::constraint::eq(arguments[3].clone(), arguments[2].clone()),
            crate::constraint::eq(arguments[4].clone(), arguments[2].clone()),
        ]
    }
}

/// Name of the [`DropReflexiveStep`] primitive.
pub(crate) const DROP_REFLEXIVE_STEP: &str = "drop-reflexive-step";

/// The `drop-reflexive-step` primitive:
/// `(drop-reflexive-step spelling column before after) -> spelling` — the
/// packed-row spelling with `column` no longer named
/// ([`Skeleton::without_column`]) when `before == after`, and `spelling` itself
/// otherwise. Typed `(String i64 T T) -> String` for any sort `T`.
///
/// `before`/`after` must be the two values the step in `column` canonicalizes
/// between: equal values are what makes that step reflexive, and so make the
/// narrowed spelling the same composition. A column the spelling stops naming
/// is carried but never read, so the caller may fill it with anything.
#[derive(Clone, Default)]
pub(crate) struct DropReflexiveStep {
    /// `(spelling, column)` -> that spelling without the column.
    dropped: Arc<Mutex<HashMap<(Value, i64), Value>>>,
}

impl crate::Primitive for DropReflexiveStep {
    fn name(&self) -> &str {
        DROP_REFLEXIVE_STEP
    }

    fn get_type_constraints(&self, span: &Span) -> Box<dyn crate::constraint::TypeConstraint> {
        Box::new(DropReflexiveStepTypeConstraint { span: span.clone() })
    }
}

impl crate::PurePrim for DropReflexiveStep {
    fn apply<'a, 'db>(&self, state: crate::PureState<'a, 'db>, args: &[Value]) -> Option<Value> {
        let [spelling, column, before, after] = args else {
            return None;
        };
        if before != after {
            return Some(*spelling);
        }
        let base_values = crate::exec_state::Core::base_values(&state);
        let key = (*spelling, base_values.unwrap::<i64>(*column));
        if let Some(dropped) = self.dropped.lock().unwrap().get(&key) {
            return Some(*dropped);
        }
        let text = base_values.unwrap::<crate::sort::S>(*spelling);
        let skeleton = Skeleton::from_spelling(text.as_str())?;
        let dropped = base_values.get::<crate::sort::S>(
            skeleton
                .without_column(key.1.try_into().ok()?)?
                .spelling()
                .into(),
        );
        self.dropped.lock().unwrap().insert(key, dropped);
        Some(dropped)
    }
}

struct DropReflexiveStepTypeConstraint {
    span: Span,
}

impl crate::constraint::TypeConstraint for DropReflexiveStepTypeConstraint {
    fn get(
        &self,
        arguments: &[crate::core::AtomTerm],
        typeinfo: &TypeInfo,
    ) -> Vec<Box<dyn crate::constraint::Constraint<crate::core::AtomTerm, crate::ArcSort>>> {
        // `(spelling column before after) -> out`: `spelling`/`out` are
        // `String`, `column` is `i64`, and `before`/`after` share one sort.
        if arguments.len() != 5 {
            return vec![crate::constraint::impossible(
                crate::constraint::ImpossibleConstraint::ArityMismatch {
                    atom: crate::core::Atom {
                        span: self.span.clone(),
                        head: DROP_REFLEXIVE_STEP.to_string(),
                        args: arguments.to_vec(),
                    },
                    expected: 5,
                },
            )];
        }
        let mut constraints = vec![crate::constraint::eq(
            arguments[3].clone(),
            arguments[2].clone(),
        )];
        if let Some(string) = typeinfo.get_sort_by_name("String") {
            constraints.push(crate::constraint::assign(
                arguments[0].clone(),
                string.clone(),
            ));
            constraints.push(crate::constraint::assign(
                arguments[4].clone(),
                string.clone(),
            ));
        }
        if let Some(int) = typeinfo.get_sort_by_name("i64") {
            constraints.push(crate::constraint::assign(arguments[1].clone(), int.clone()));
        }
        constraints
    }
}
