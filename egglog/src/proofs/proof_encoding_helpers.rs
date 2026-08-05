//! Proof encoding helper functions that handle
//! naming, headers, and checking whether a program supports proof encoding.

use std::path::Path;

use crate::{
    EGraph, TypeInfo, Value,
    ast::{
        Command, Expr, Fact, GenericCommand, ResolvedAction, ResolvedCommand, ResolvedExpr,
        ResolvedExprExt, ResolvedFact, ResolvedNCommand, Schedule, Span,
    },
    core::ResolvedCall,
    proofs::proof_encoding::ProofInstrumentor,
    util::{FreshGen, HashMap, HashSet, SymbolGen},
};

/// Holds all the names used in proof encoding.
/// We need fresh names that don't collide with user-defined names.
/// All of these names should be generated with the single global [`SymbolGen`].
#[derive(Clone)]
pub(crate) struct EncodingNames {
    pub(crate) ast_sort: String,
    pub(crate) proof_datatype: String,
    pub(crate) fiat_constructor: String,
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
    pub(crate) container_normalize_constructor: String,
    pub(crate) eval_constructor: String,
    /// For a given function symbol, the name of the function that converts to the AST type.
    pub(crate) sort_to_ast_constructor: HashMap<String, String>,
    pub(crate) fn_to_term_sort: HashMap<String, String>,
    // Ruleset names
    pub(crate) path_compress_ruleset_name: String,
    pub(crate) rebuilding_ruleset_name: String,
    pub(crate) rebuilding_cleanup_ruleset_name: String,
    pub(crate) delete_subsume_ruleset_name: String,
    // Per-function fresh names
    pub(crate) view_name: HashMap<String, String>,
    pub(crate) to_delete_name: HashMap<String, String>,
    pub(crate) subsumed_name: HashMap<String, String>,
    pub(crate) term_proof_name: HashMap<String, String>,
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
}

/// The composition one packed proof row stands for, written over the row's own
/// proof columns: a leaf is the proof in a column, so the skeleton is also the
/// row's layout. Every column is named, so a column a composition reaches twice
/// is named twice and carried once.
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
            ProofTree::Sym(inner) => inner.width(),
            ProofTree::Trans(left, right) | ProofTree::Congr(left, _, right) => {
                left.width().max(right.width())
            }
        }
    }

    fn collect_columns(&self, columns: &mut Vec<usize>) {
        match self {
            ProofTree::Leaf(column) => columns.push(*column),
            ProofTree::Sym(inner) => inner.collect_columns(columns),
            ProofTree::Trans(left, right) | ProofTree::Congr(left, _, right) => {
                left.collect_columns(columns);
                right.collect_columns(columns);
            }
        }
    }

    /// This skeleton as the string a packed row carries: its nodes in prefix
    /// order, one `_`-separated token each — `sym`, `trans`, `congr`,
    /// `p<column>` for a column, and a bare number for a congruence's child
    /// position. Panics unless [`Self::from_spelling`] reads it back, since that
    /// is all unpacking has to go on.
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
        }
    }

    /// The skeleton [`Self::spelling`] writes as `spelling`, or `None` when that
    /// is not a spelling of one whose columns are `0..n`. A column may be named
    /// more than once: a composition reaching the same step twice carries it
    /// once.
    pub(crate) fn from_spelling(spelling: &str) -> Option<Skeleton> {
        let mut tokens = spelling.split('_');
        let skeleton = Skeleton::read(&mut tokens)?;
        if tokens.next().is_some() {
            return None;
        }
        let mut columns = vec![];
        skeleton.collect_columns(&mut columns);
        columns.sort_unstable();
        columns.dedup();
        (columns == (0..columns.len()).collect::<Vec<_>>()).then_some(skeleton)
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
    /// conversion). It embeds no AST, so it needs neither the merged term
    /// nor the function key/children — usable in a `:merge` action.
    MergeIdx(String, String, String, usize),
    /// Term-free merge justification for the whole view row (function name + two
    /// premise proof expressions). The conclusion `f(children, merged)` is
    /// reconstructed during proof conversion by running the whole merge body on
    /// the premise outputs; no AST/children needed.
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
            ast_sort: symbol_gen.fresh("Ast"),
            proof_datatype: symbol_gen.fresh("Proof"),
            fiat_constructor: symbol_gen.fresh("Fiat"),
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
            container_normalize_constructor: symbol_gen.fresh("ContainerNormalize"),
            eval_constructor: symbol_gen.fresh("Eval"),
            sort_to_ast_constructor: HashMap::default(),
            fn_to_term_sort: HashMap::default(),
            path_compress_ruleset_name: symbol_gen.fresh("parent"),
            rebuilding_ruleset_name: symbol_gen.fresh("rebuilding"),
            rebuilding_cleanup_ruleset_name: symbol_gen.fresh("rebuilding_cleanup"),
            delete_subsume_ruleset_name: symbol_gen.fresh("delete_subsume_ruleset"),
            view_name: HashMap::default(),
            to_delete_name: HashMap::default(),
            subsumed_name: HashMap::default(),
            term_proof_name: HashMap::default(),
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
        let res = self.egraph.parser.get_program_from_string(None, input);
        self.egraph.parser.ensure_no_reserved_symbols = true;

        res.unwrap()
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
    /// that no earlier program declared. A rule's premise count is its body-fact
    /// count, so the arities a program uses are known before it is encoded; these
    /// are emitted ahead of the program's own commands.
    pub(crate) fn rule_arity_header(&mut self, program: &[ResolvedNCommand]) -> Vec<Command> {
        fn collect(commands: &[ResolvedNCommand], out: &mut Vec<usize>) {
            for command in commands {
                match command {
                    ResolvedNCommand::NormRule { rule } => out.push(rule.body.len()),
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
            self.proof_names().delete_subsume_ruleset_name
        );
        self.parse_program(&str)
    }

    /// Internal parse helper for term encoding- parse and crash on failure.
    pub(crate) fn parse_schedule(&mut self, input: String) -> Schedule {
        self.egraph.parser.ensure_no_reserved_symbols = false;
        let res = self.egraph.parser.get_schedule_from_string(None, &input);
        self.egraph.parser.ensure_no_reserved_symbols = true;
        res.unwrap()
    }

    /// Internal parse helper for term encoding- parse and crash on failure.
    pub(crate) fn parse_facts(&mut self, input: &[String]) -> Vec<Fact> {
        self.egraph.parser.ensure_no_reserved_symbols = false;
        let res = input
            .iter()
            .map(|f| self.egraph.parser.get_fact_from_string(None, f).unwrap())
            .collect();
        self.egraph.parser.ensure_no_reserved_symbols = true;
        res
    }

    /// Internal parse helper for term encoding- parse an expression and crash on failure.
    pub(crate) fn parse_expr(&mut self, input: &str) -> Expr {
        self.egraph.parser.ensure_no_reserved_symbols = false;
        let res = self.egraph.parser.get_expr_from_string(None, input);
        self.egraph.parser.ensure_no_reserved_symbols = true;
        res.unwrap()
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

    pub(crate) fn delete_name(&mut self, name: &str) -> String {
        if let Some(n) = self.egraph.proof_state.proof_names.to_delete_name.get(name) {
            n.clone()
        } else {
            let fresh_name = self
                .egraph
                .parser
                .symbol_gen
                .fresh(&format!("to_delete_{name}"));
            self.egraph
                .proof_state
                .proof_names
                .to_delete_name
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

    /// Returns code for a constructor that converts from sort to AST.
    /// Adds to the sort to AST constructor map.
    pub(crate) fn add_to_ast(&mut self, sort: &str) -> String {
        if self.proofs_enabled() {
            // Check if we've already created an AST constructor for this sort
            if self
                .egraph
                .proof_state
                .proof_names
                .sort_to_ast_constructor
                .contains_key(sort)
            {
                // Return empty string since the constructor already exists
                return "".to_string();
            }

            let to_ast_constructor = self.egraph.parser.symbol_gen.fresh(&format!("Ast{sort}"));
            self.egraph
                .proof_state
                .proof_names
                .sort_to_ast_constructor
                .insert(sort.to_string(), to_ast_constructor.clone());
            let ast_sort = &self.proof_names().ast_sort;
            format!(
                "(function {to_ast_constructor} ({sort} {ast_sort}) Unit :no-merge :internal-hidden :internal-term-node)"
            )
        } else {
            "".to_string()
        }
    }

    /// Given a function name, returns the name of the AST constructor for that function's sort.
    pub(crate) fn fname_to_ast_name(&self, fname: &str) -> &str {
        let fn_sort = self
            .proof_names()
            .fn_to_term_sort
            .get(fname)
            .unwrap_or_else(|| panic!("Function {fname} has no recorded sort"))
            .clone();
        self.proof_names()
            .sort_to_ast_constructor
            .get(&fn_sort)
            .unwrap_or_else(|| {
                panic!("Function {fname}'s sort {fn_sort} has no recorded AST constructor")
            })
    }

    pub(crate) fn term_proof_name(&mut self, name: &str) -> String {
        if let Some(n) = self
            .egraph
            .proof_state
            .proof_names
            .term_proof_name
            .get(name)
        {
            n.clone()
        } else {
            let fresh_name = self.egraph.parser.symbol_gen.fresh(&format!("{name}Proof"));
            self.egraph
                .proof_state
                .proof_names
                .term_proof_name
                .insert(name.to_string(), fresh_name.clone());
            fresh_name
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
        let mut to_ast_constructors = Vec::new();
        // need to build a Ast{lit} for each lit sort in self
        for sort_name in self.egraph.type_info.sorts.keys().clone() {
            if !self
                .proof_names()
                .sort_to_ast_constructor
                .contains_key(sort_name)
            {
                let ast_constructor = self
                    .egraph
                    .parser
                    .symbol_gen
                    .fresh(&format!("Ast{sort_name}"));
                self.egraph
                    .proof_state
                    .proof_names
                    .sort_to_ast_constructor
                    .insert(sort_name.clone(), ast_constructor.clone());
                to_ast_constructors.push(format!(
                    "(function {ast_constructor} ({sort_name} {}) Unit :no-merge :internal-hidden :internal-term-node)",
                    self.proof_names().ast_sort
                ));
            }
        }
        let to_ast_str = to_ast_constructors.join("\n");

        let EncodingNames {
            ref ast_sort,
            ref proof_datatype,
            ref fiat_constructor,
            ref rule_link_constructor,
            ref merge_fn_idx_constructor,
            ref merge_fn_row_constructor,
            ref eq_trans_constructor,
            ref eq_sym_constructor,
            ref congr_constructor,
            ref congr_all_constructor,
            ref container_normalize_constructor,
            ref eval_constructor,
            ..
        } = *self.proof_names();

        format!(
            "
(sort {ast_sort}) ;; wrap sorts in this for proofs
;; The proof datatype records the global proof constructor names so container
;; rebuild can recover them on re-parse (see ContainerRebuildSpec).
(sort {proof_datatype} :internal-proof-names {congr_constructor} {congr_all_constructor} {eq_trans_constructor} {eq_sym_constructor} {container_normalize_constructor} {fiat_constructor})

;; Proof/AST terms are relations, not constructors: the encoding mints a fresh id
;; (`get-fresh!`) and asserts the row, so congruent duplicates are kept (never
;; merged away) rather than relying on native congruence. The final column of each
;; relation is the minted output id.

{to_ast_str}

;; Fiat justification for globals and primitives, gives two terms t1 = t2 for the proposition being justified
(function {fiat_constructor} ({ast_sort} {ast_sort} {proof_datatype}) Unit :no-merge :internal-hidden :internal-term-node)
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
        "sort has a presort (custom sort container implementation). Custom sorts are not supported by proof encoding."
    )]
    SortWithPresort,
    #[error(
        "sort has a :internal-uf annotation. The :internal-uf annotation is used internally by term encoding and cannot be specified manually in proof mode."
    )]
    SortWithUfAnnotation,
    #[error(
        "sort has a :internal-proof-func annotation. The :internal-proof-func annotation is used internally by proof encoding and cannot be specified manually in proof mode."
    )]
    SortWithProofFuncAnnotation,
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
        "a `:merge` action block (actions before the result value) is not supported by the term/proof encoding."
    )]
    MergeActionBlock,
    #[error("checked alias expression is unsupported: {0}")]
    CheckedAliasExpression(String),
    #[error(
        "eq-sort-output `:no-merge` functions are not supported by the term/proof encoding (their conflict check needs union-find leaders); run them on the native backend, or give the function a `:merge` (e.g. `:merge old`). Primitive/`Unit`-output `:no-merge` functions are supported."
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

/// Check if a fact contains a primitive expression whose result needs a stored term proof.
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

fn checked_alias_expr_support(
    expr: &ResolvedExpr,
    type_info: &TypeInfo,
) -> Result<(), ProofEncodingUnsupportedReason> {
    match expr {
        ResolvedExpr::Lit(..) => Ok(()),
        // `let-check` is typechecked with only previously published checked
        // aliases in its local binding environment. Preserve those variables
        // as graph-local constants: expanding their constructor syntax would
        // repeat a lookup and can fail after a selected delete even though the
        // alias still owns the value it checked.
        ResolvedExpr::Var(_, variable) if !variable.is_global_ref => Ok(()),
        ResolvedExpr::Var(_, variable) => {
            Err(ProofEncodingUnsupportedReason::CheckedAliasExpression(
                format!("global variable `{}` is not a checked alias", variable.name),
            ))
        }
        ResolvedExpr::Call(_, ResolvedCall::Values(_), _) => {
            Err(ProofEncodingUnsupportedReason::CheckedAliasExpression(
                "tuple values are not supported".to_owned(),
            ))
        }
        ResolvedExpr::Call(_, ResolvedCall::Func(function), children) => {
            let supported = function.outputs.len() == 1
                && match function.subtype {
                    crate::ast::FunctionSubtype::Constructor => function.output().is_eq_sort(),
                    crate::ast::FunctionSubtype::Custom => true,
                };
            if !supported {
                return Err(ProofEncodingUnsupportedReason::CheckedAliasExpression(
                    format!(
                        "function `{}` is not a readable single-output function",
                        function.name
                    ),
                ));
            }
            for child in children {
                checked_alias_expr_support(child, type_info)?;
            }
            Ok(())
        }
        ResolvedExpr::Call(_, ResolvedCall::Primitive(primitive), children) => {
            if !primitive.is_pure() || primitive.validator().is_none() {
                return Err(ProofEncodingUnsupportedReason::CheckedAliasExpression(
                    format!(
                        "primitive `{}` is not replay-safe and pure",
                        primitive.name()
                    ),
                ));
            }
            if primitive.output().is_container_sort()
                && !type_info
                    .checked_alias_container_sorts
                    .contains(primitive.output().name())
            {
                return Err(ProofEncodingUnsupportedReason::CheckedAliasExpression(
                    format!(
                        "primitive `{}` returns unsupported container sort `{}`",
                        primitive.name(),
                        primitive.output().name()
                    ),
                ));
            }
            for child in children {
                checked_alias_expr_support(child, type_info)?;
            }
            Ok(())
        }
    }
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

    // A container built by a primitive in the query is a side condition with no
    // carryable proof, so it can't be used in an action. Reject a rule that binds
    // such a container to a variable used in its actions.
    if let GenericCommand::Rule { rule } = command {
        let mut constructed: Vec<String> = Vec::new();
        for fact in &rule.body {
            if let ResolvedFact::Eq(_, lhs, rhs) = fact {
                for (var_side, call_side) in [(lhs, rhs), (rhs, lhs)] {
                    if let ResolvedExpr::Var(_, v) = var_side
                        && let ResolvedExpr::Call(_, ResolvedCall::Primitive(prim), _) = call_side
                        && prim.output().is_eq_container_sort()
                    {
                        constructed.push(v.name.clone());
                    }
                }
            }
        }
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
        GenericCommand::Sort {
            proof_func: Some(_),
            ..
        } => Err(ProofEncodingUnsupportedReason::SortWithProofFuncAnnotation),
        GenericCommand::UserDefined(..) => Err(ProofEncodingUnsupportedReason::UserDefinedCommand),
        GenericCommand::LetCheck { expr, .. } => checked_alias_expr_support(expr, type_info),
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
