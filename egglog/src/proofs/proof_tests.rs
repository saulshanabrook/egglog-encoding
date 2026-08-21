#[cfg(test)]
mod tests {
    use crate::ast::{
        GenericAction, GenericNCommand, Literal, ResolvedAction, ResolvedCommand, ResolvedExpr,
        ResolvedFact, RuleEvalMode, remove_globals::remove_globals, sanitize_internal_names,
    };
    use crate::core::ResolvedCall;
    use crate::proofs::proof_checker::eval_expr_with_subst;
    use crate::proofs::proof_encoding_helpers::recomputable_premises;
    use crate::proofs::proof_extraction::ProveExistsError;
    use crate::proofs::proof_format::{ProofId, ProofStore, Proposition};
    use crate::proofs::proof_head::{Firing, HeadPlan, HeadProof, ProofAlgebra};
    use crate::typechecking::TypeError;
    use crate::util::{HashMap, HashSet, IndexMap, SymbolGen};
    use crate::{
        CommandOutput, EGraph, Error, ProofEncodingUnsupportedReason, TermDag, TermId,
        add_primitive, add_primitive_with_validator,
    };

    fn term_encode(source: &str) -> Vec<ResolvedCommand> {
        let mut egraph = crate::EGraph::new_with_term_encoding();
        egraph.resolve_program(None, source).unwrap()
    }

    /// A bridge supply for a firing where every term the head builds is new, so
    /// each one interns into itself. It never runs dry, so a walk drawing on it
    /// reaches the end of the head.
    fn interns_into_itself(store: &mut ProofStore, to_canonical: ProofId) -> Option<ProofId> {
        Some(store.reflexive(to_canonical))
    }

    /// Stand a distinct constant in for every variable a rule head reads but
    /// does not itself bind, so the head can be processed without a match.
    fn head_input_bindings(
        actions: &[ResolvedAction],
        term_dag: &mut TermDag,
    ) -> HashMap<String, TermId> {
        fn read(expr: &ResolvedExpr, bound: &HashSet<String>, inputs: &mut Vec<String>) {
            expr.visit_vars(&mut |_, var| {
                if !bound.contains(&var.name) && !inputs.contains(&var.name) {
                    inputs.push(var.name.clone());
                }
            });
        }
        let mut bound: HashSet<String> = HashSet::default();
        let mut inputs = vec![];
        for action in actions {
            match action {
                GenericAction::Let(_, var, expr) => {
                    read(expr, &bound, &mut inputs);
                    bound.insert(var.name.clone());
                }
                GenericAction::Expr(_, expr) => read(expr, &bound, &mut inputs),
                GenericAction::Union(_, lhs, rhs) => {
                    read(lhs, &bound, &mut inputs);
                    read(rhs, &bound, &mut inputs);
                }
                GenericAction::Set(_, _, args, value) => {
                    for arg in args {
                        read(arg, &bound, &mut inputs);
                    }
                    read(value, &bound, &mut inputs);
                }
                GenericAction::Panic(..) | GenericAction::Change(..) => {}
            }
        }
        inputs
            .into_iter()
            .map(|name| {
                let term = term_dag.app(name.clone(), vec![]);
                (name, term)
            })
            .collect()
    }

    /// A rule head's proofs are the flat array the encoder names positions of and
    /// proof conversion rebuilds, so the array has to reach everything the head
    /// concludes — nothing may be left with no column to be named by. Pin it:
    /// walking each head states every proposition processing that head derives.
    #[test]
    fn walking_a_rule_head_states_every_proposition_it_concludes() {
        let source = r#"
            (datatype Math (Num i64) (Add Math Math) (Neg Math))
            (relation Seen (Math))
            (function Cost (Math) i64 :no-merge)

            (Add (Num 1) (Num 2))

            (rule ((= e (Add a b)))
                  ((union e (Add b a)))
                  :name "commute")

            (rule ((= e (Add a b)))
                  ((let inner (Neg a))
                   (let outer (Add inner b))
                   (union e outer)
                   (Seen outer))
                  :name "nest")

            (rule ((= e (Num n)))
                  ((set (Cost e) 1))
                  :name "cost")

            ;; A `union` neither of whose operands is a matched variable, so the
            ;; orientation check has to read both operands' own conclusions.
            (rule ((Seen s))
                  ((union (Neg s) (Add s s)))
                  :name "both_built")

            (run 2)
            (prove (= (Add (Num 1) (Num 2)) (Add (Num 2) (Num 1))))
        "#;

        let mut egraph = EGraph::new_with_proofs();
        egraph.parse_and_run_program(None, source).unwrap();

        let rules: Vec<_> = egraph
            .proof_check_program
            .iter()
            .filter_map(|cmd| match cmd {
                GenericNCommand::NormRule { rule } => Some(rule),
                _ => None,
            })
            .collect();
        let names: Vec<_> = rules.iter().map(|rule| rule.name.as_str()).collect();
        for expected in ["commute", "nest", "cost", "both_built"] {
            assert!(
                names.contains(&expected),
                "rule '{expected}' not in {names:?}"
            );
        }

        for rule in rules {
            let actions = &rule.head.0;
            let mut term_dag = TermDag::default();
            let inputs = head_input_bindings(actions, &mut term_dag);

            let mut minted = 0usize;
            let mut fresh = || {
                minted += 1;
                format!("@union-operand-{minted}")
            };
            let plan = HeadPlan::new(actions, &mut fresh);
            let mut store = ProofStore::new(term_dag, HashMap::default(), HashSet::default());
            let expected = head_conclusions(&rule.name, actions, inputs.clone(), &mut store);
            // No premises, and every term the head builds interns into itself, so
            // each column states the head's conclusion there rather than one about
            // an e-class it interned into — and the walk reaches the whole head.
            let mut firing = Firing::new(
                &rule.name,
                &plan,
                inputs,
                vec![],
                IndexMap::default(),
                Box::new(interns_into_itself),
            );
            let columns: Vec<_> = firing
                .proofs(&mut store)
                .iter()
                .flatten()
                .copied()
                .collect();
            let stated: HashSet<_> = columns
                .into_iter()
                .map(|proof| store.get(proof).proposition().clone())
                .collect();
            for (what, prop) in expected {
                assert!(
                    stated.contains(&prop),
                    "rule '{}' concludes {what}, which no column of its head states",
                    rule.name
                );
            }
        }
    }

    /// The encoder names each rule proof row by the column its walk of the head
    /// is at, and proof conversion reads that column out of the array [`Firing`]
    /// builds by walking the same head. Both claim their runs from
    /// [`HeadLayout`], which checks the position each is at as it goes, so the
    /// two cannot disagree about a run's length. Pin what is left: every column
    /// an encoded head writes names a proof the walk produces, and one the head
    /// writes a row for — so a numbering that slipped within a run fails here.
    #[test]
    fn every_column_an_encoded_head_writes_is_one_the_walk_produces() {
        let source = r#"
            (datatype Math (Num i64) (Add Math Math) (Neg Math))
            (relation Seen (Math))
            (function Cost (Math) i64 :no-merge)
            (let g (Num 7))

            (Add (Num 1) (Num 2))

            (rule ((= e (Add a b)))
                  ((union e (Add b a)))
                  :name "commute")

            (rule ((= e (Add a b)))
                  ((let inner (Neg a))
                   (let outer (Add inner b))
                   (union e outer)
                   (Seen outer))
                  :name "nest")

            (rule ((= e (Num n)))
                  ((set (Cost e) 1))
                  :name "cost")

            ;; A head reading a global, so `remove_globals` appends a body fact.
            (rule ((Seen s))
                  ((Seen (Add s g)))
                  :name "with_global")

            ;; A `union` of two matched variables: neither operand is built, so
            ;; the orientation reads both endpoints' own conclusions.
            (rule ((= e (Add a b)) (= f (Add b a)))
                  ((union e f))
                  :name "matched_union")

            ;; A second `union` on an already-optimized variable stays a `union`,
            ;; with a connector on each operand, so the orientation reads two
            ;; composed columns.
            (rule ((Seen s))
                  ((let p (Neg s))
                   (union p s)
                   (union p (Add s s)))
                  :name "chained_union")
        "#;

        // Nothing above runs, so the columns below are read by this test alone
        // rather than by proof conversion firing the rules.
        //
        // The rules as the checker replays them: the heads [`Firing`] walks.
        let mut checker = EGraph::new_with_proofs();
        checker.parse_and_run_program(None, source).unwrap();
        let written: HashMap<&str, &crate::ast::ResolvedRule> = checker
            .proof_check_program
            .iter()
            .filter_map(|cmd| match cmd {
                GenericNCommand::NormRule { rule } => Some((rule.name.as_str(), rule)),
                _ => None,
            })
            .collect();

        let mut encoder = EGraph::new_with_proofs();
        let commands = encoder.resolve_program(None, source).unwrap();
        let names = encoder.proof_state.proof_names.clone();

        let mut covered: Vec<(&str, usize)> = vec![];
        for command in &commands {
            let ResolvedCommand::Rule { rule } = command else {
                continue;
            };
            let Some(walked) = written.get(rule.name.as_str()) else {
                continue;
            };
            // Every rule proof row the head writes: `(mint-Rule_k! … col)` or
            // `(mint-RuleLink! prev bridge col)`. The column is the last
            // argument, as a literal or as the `proof-of-max` over the two
            // columns a `union` orients between.
            let columns: Vec<i64> = rule
                .head
                .0
                .iter()
                .filter_map(|action| {
                    let (relation, args) = mint_call(action)?;
                    (names.fused_rule_arity(relation).is_some()
                        || relation == names.rule_link_constructor)
                        .then(|| args.last())
                        .flatten()
                })
                .flat_map(|column| {
                    let mut out = vec![];
                    int_literals(column, &mut out);
                    out
                })
                .collect();
            if columns.is_empty() {
                continue;
            }

            let actions = &walked.head.0;
            let mut term_dag = TermDag::default();
            let inputs = head_input_bindings(actions, &mut term_dag);
            let mut minted = 0usize;
            let mut fresh = || {
                minted += 1;
                format!("@union-operand-{minted}")
            };
            let plan = HeadPlan::new(actions, &mut fresh);
            let layout = &plan.layout;
            let mut store = ProofStore::new(term_dag, HashMap::default(), HashSet::default());
            let mut firing = Firing::new(
                &walked.name,
                &plan,
                inputs,
                vec![],
                IndexMap::default(),
                Box::new(interns_into_itself),
            );
            let filled: Vec<bool> = firing
                .proofs(&mut store)
                .iter()
                .map(Option::is_some)
                .collect();

            let mut named = 0usize;
            for column in &columns {
                // `-1` is the encoder's placeholder for a position the head
                // concludes nothing about, whose proof nothing reads back.
                if *column < 0 {
                    continue;
                }
                let column = *column as usize;
                assert!(
                    filled.get(column).copied().unwrap_or(false),
                    "rule '{}' writes column {column}, which its head walk does not \
                     produce (columns filled: {filled:?})",
                    rule.name
                );
                // A head writes no row for a guest's dropped `union` — that is
                // folded into the view row beside it — so a column landing on one
                // is a column the walk numbers differently.
                let held = layout.proof_at(column);
                assert!(
                    !matches!(held, Some(HeadProof::DroppedEdge)),
                    "rule '{}' writes column {column}, which its head walk fills \
                     with {held:?} — a proof no head writes a row for",
                    rule.name
                );
                named += 1;
            }
            covered.push((rule.name.as_str(), named));
        }

        // Guard against a vacuous pass: every rule above must write a numbered
        // column, so a head that stops writing them fails here rather than
        // silently dropping out of the check.
        for expected in [
            "commute",
            "nest",
            "cost",
            "with_global",
            "matched_union",
            "chained_union",
        ] {
            let named = covered
                .iter()
                .find(|(name, _)| *name == expected)
                .map(|(_, named)| *named)
                .unwrap_or_else(|| {
                    panic!("rule '{expected}' wrote no rule proof row: {covered:?}")
                });
            assert!(
                named > 0,
                "rule '{expected}' wrote only unnumbered columns: {covered:?}"
            );
        }
    }

    /// The relation `action` mints a row of, with the row's arguments (the
    /// minted id excluded); `None` for any other action.
    fn mint_call(action: &ResolvedAction) -> Option<(&str, &[ResolvedExpr])> {
        let ResolvedAction::Let(_, _, ResolvedExpr::Call(_, ResolvedCall::Primitive(prim), args)) =
            action
        else {
            return None;
        };
        let relation = crate::proofs::proof_fresh::mint_prim_relation(prim.name())?;
        Some((relation, args))
    }

    /// Every integer literal in `expr`, in order.
    fn int_literals(expr: &ResolvedExpr, out: &mut Vec<i64>) {
        match expr {
            ResolvedExpr::Lit(_, Literal::Int(n)) => out.push(*n),
            ResolvedExpr::Call(_, _, args) => {
                for arg in args {
                    int_literals(arg, out);
                }
            }
            ResolvedExpr::Lit(..) | ResolvedExpr::Var(..) => {}
        }
    }

    /// What a rule head concludes, derived independently of the walk that
    /// produces its proofs: every call it evaluates exists, and every `union`
    /// holds in both directions.
    fn head_conclusions(
        rule_name: &str,
        actions: &[ResolvedAction],
        mut bindings: HashMap<String, TermId>,
        store: &mut ProofStore,
    ) -> Vec<(String, Proposition)> {
        fn eval(
            rule_name: &str,
            expr: &ResolvedExpr,
            bindings: &HashMap<String, TermId>,
            store: &mut ProofStore,
        ) -> TermId {
            eval_expr_with_subst(rule_name, expr, &mut store.term_dag, bindings)
                .unwrap_or_else(|e| panic!("rule '{rule_name}' head did not evaluate: {e}"))
                .0
        }
        fn exists(
            rule_name: &str,
            expr: &ResolvedExpr,
            bindings: &HashMap<String, TermId>,
            store: &mut ProofStore,
            out: &mut Vec<(String, Proposition)>,
        ) {
            let ResolvedExpr::Call(_, _, args) = expr else {
                return;
            };
            for arg in args {
                exists(rule_name, arg, bindings, store, out);
            }
            let term = eval(rule_name, expr, bindings, store);
            out.push((format!("that {expr} exists"), Proposition::new(term, term)));
        }

        let mut out = vec![];
        for action in actions {
            match action {
                GenericAction::Let(_, var, expr) => {
                    exists(rule_name, expr, &bindings, store, &mut out);
                    let term = eval(rule_name, expr, &bindings, store);
                    bindings.insert(var.name.clone(), term);
                }
                GenericAction::Expr(_, expr) => exists(rule_name, expr, &bindings, store, &mut out),
                GenericAction::Union(_, lhs, rhs) => {
                    exists(rule_name, lhs, &bindings, store, &mut out);
                    exists(rule_name, rhs, &bindings, store, &mut out);
                    let lhs_term = eval(rule_name, lhs, &bindings, store);
                    let rhs_term = eval(rule_name, rhs, &bindings, store);
                    out.push((
                        format!("{lhs} = {rhs}"),
                        Proposition::new(lhs_term, rhs_term),
                    ));
                    out.push((
                        format!("{rhs} = {lhs}"),
                        Proposition::new(rhs_term, lhs_term),
                    ));
                }
                GenericAction::Set(span, func, args, value) => {
                    let mut row = args.to_vec();
                    row.push(value.clone());
                    let row = ResolvedExpr::Call(span.clone(), func.clone(), row);
                    exists(rule_name, &row, &bindings, store, &mut out);
                }
                GenericAction::Panic(..) | GenericAction::Change(..) => {}
            }
        }
        out
    }

    /// A rule proof records no terms, so a body variable bound to a value the
    /// body computed — a primitive's result, a container's — reaches the
    /// checker only by replaying the rule. Each case below binds one that way
    /// and proves a conclusion that needs it.
    #[test]
    fn rule_proofs_check_with_computed_body_values() {
        let cases = [
            // a computed String
            r#"(relation Strings (String String))
               (Strings "hello" "world")
               (rule ((Strings a b) (= res (+ a " " b)))
                     ((Strings "found" "hello world")) :name "concat")
               (run 1)
               (prove (Strings "found" "hello world"))"#,
            // a non-eq container matched in the body and read
            r#"(sort IVec (Vec i64))
               (relation HasVec (IVec))
               (relation VLen (i64))
               (HasVec (vec-of 1 2 3))
               (rule ((HasVec v) (= n (vec-length v))) ((VLen n)) :name "vec-len")
               (run 1)
               (prove (VLen 3))"#,
            // a non-eq container whose read computes a base value
            r#"(sort SMap (Map String i64))
               (relation HasMap (SMap))
               (relation MapVal (i64))
               (HasMap (map-insert (map-empty) "a" 7))
               (rule ((HasMap m) (= v (map-get m "a"))) ((MapVal v)) :name "map-get")
               (run 1)
               (prove (MapVal 7))"#,
        ];

        for source in cases {
            let mut egraph = EGraph::new_with_proofs();
            egraph
                .parse_and_run_program(None, source)
                .unwrap_or_else(|e| panic!("{source}\nfailed: {e}"));
        }
    }

    /// The encoding reads `@UF` from rule actions under
    /// `:unsafe-seminaive` — in user rule heads and in the indexed rebuild
    /// rule. Assert this produces the same database as the safe baseline (the
    /// same rules annotated `:naive`), for a hardcoded handful of files
    /// (running it across all tests would be too slow).
    #[test]
    fn unsafe_seminaive_matches_naive() {
        let files = [
            "tests/calc.egg",
            "tests/integer_math.egg",
            "tests/fibonacci-demand.egg",
            "tests/until.egg",
        ];

        for file in files {
            let source = std::fs::read_to_string(file)
                .unwrap_or_else(|e| panic!("couldn't read {file}: {e}"));

            let encode = |naive: bool| -> String {
                let mut egraph = crate::EGraph::new_with_proofs();
                egraph.proof_state.force_proof_naive = naive;
                egraph
                    .resolve_program(Some(file.to_string()), &source)
                    .unwrap_or_else(|e| panic!("{file} resolve (naive={naive}) failed: {e}"))
                    .iter()
                    .map(|cmd| cmd.to_string())
                    .collect::<Vec<_>>()
                    .join("\n")
            };

            // Guard against a vacuous comparison: both `:unsafe-seminaive`
            // sites must be present, and the knob must flip every one of them,
            // since a rule left `:unsafe-seminaive` runs identically on both
            // sides. Only the rebuild rules carry `:internal-include-subsumed`.
            let unsafe_encoding = encode(false);
            let (rebuild, rule_head): (Vec<&str>, Vec<&str>) = unsafe_encoding
                .lines()
                .filter(|line| line.contains(":unsafe-seminaive"))
                .partition(|line| line.contains(":internal-include-subsumed"));
            assert!(
                !rule_head.is_empty(),
                "expected {file} to encode a rule head `:unsafe-seminaive`"
            );
            assert!(
                !rebuild.is_empty(),
                "expected {file} to encode the rebuild rule `:unsafe-seminaive`"
            );
            assert!(
                !encode(true).contains(":unsafe-seminaive"),
                "`force_proof_naive` left `:unsafe-seminaive` in {file}, so the \
                 comparison does not cover those rules"
            );

            // `print-size` summarizes the whole database (per-function row
            // counts, sorted) deterministically.
            let program = format!("{source}\n(print-size)");

            let run = |naive: bool| -> Vec<CommandOutput> {
                let mut egraph = crate::EGraph::new_with_proofs();
                egraph.proof_state.force_proof_naive = naive;
                egraph
                    .parse_and_run_program(Some(file.to_string()), &program)
                    .unwrap_or_else(|e| panic!("{file} (naive={naive}) failed: {e}"))
            };

            let unsafe_seminaive = CommandOutput::snapshot_stable_under_proof_encoding(&run(false));
            let naive = CommandOutput::snapshot_stable_under_proof_encoding(&run(true));

            assert_eq!(
                unsafe_seminaive, naive,
                ":unsafe-seminaive and :naive proof encodings disagree for {file}"
            );
        }
    }

    /// A user rule marked `:naive` must stay `:naive` through proof encoding;
    /// dropping it would silently switch the rule to seminaive evaluation.
    #[test]
    fn proof_encoding_preserves_naive() {
        // The second case binds an eq-sort body var. Both must stay naive.
        let cases = [
            r#"(relation r (i64))
               (relation s (i64))
               (rule ((r x)) ((s x)) :naive :name "keep")"#,
            r#"(sort Math)
               (constructor Num (i64) Math)
               (constructor Neg (Math) Math)
               (relation seen (Math))
               (rule ((Neg m)) ((seen m)) :naive :name "keep")"#,
        ];
        for source in cases {
            let mut egraph = crate::EGraph::new_with_proofs();
            let resolved = egraph.resolve_program(None, source).unwrap();
            let rule = resolved
                .iter()
                .find_map(|c| match c {
                    ResolvedCommand::Rule { rule } if rule.name == "keep" => Some(rule),
                    _ => None,
                })
                .expect("instrumented rule not found");
            assert_eq!(
                rule.eval_mode,
                RuleEvalMode::Naive,
                "proof encoding did not preserve :naive for:\n{source}"
            );
        }
    }

    #[test]
    fn proof_encoding_hoists_unnamed_rule_name_in_actions() {
        let source = r#"
            (datatype VeryLongExpressionForRuleNameHoisting
              (VeryLongLeafConstructorForRuleNameHoisting i64)
              (VeryLongUnaryConstructorForRuleNameHoisting VeryLongExpressionForRuleNameHoisting)
              (VeryLongBinaryConstructorForRuleNameHoisting
                VeryLongExpressionForRuleNameHoisting
                VeryLongExpressionForRuleNameHoisting))
            (relation VeryLongSeedRelationForRuleNameHoisting
              (VeryLongExpressionForRuleNameHoisting))

            (VeryLongSeedRelationForRuleNameHoisting
              (VeryLongLeafConstructorForRuleNameHoisting 1))

            (rule
              ((VeryLongSeedRelationForRuleNameHoisting original))
              ((let wrapped
                 (VeryLongUnaryConstructorForRuleNameHoisting original))
               (let paired
                 (VeryLongBinaryConstructorForRuleNameHoisting wrapped original))
               (union wrapped paired)))

            (run 1)
            (prove
              (= (VeryLongUnaryConstructorForRuleNameHoisting
                   (VeryLongLeafConstructorForRuleNameHoisting 1))
                 (VeryLongBinaryConstructorForRuleNameHoisting
                   (VeryLongUnaryConstructorForRuleNameHoisting
                     (VeryLongLeafConstructorForRuleNameHoisting 1))
                   (VeryLongLeafConstructorForRuleNameHoisting 1))))
        "#;

        let mut egraph = EGraph::new_with_proofs();
        let commands = egraph.resolve_program(None, source).unwrap();
        // Only the rows carrying premises inline name the rule; a later column's
        // link reads the name off the row it chains onto.
        let names = &egraph.proof_state.proof_names;
        let rule_constructors: HashSet<String> = names
            .rule_fused_declared
            .iter()
            .map(|arity| names.fused_rule(*arity))
            .collect();
        let rule = commands
            .iter()
            .find_map(|command| match command {
                ResolvedCommand::Rule { rule }
                    if rule
                        .name
                        .contains("VeryLongSeedRelationForRuleNameHoisting") =>
                {
                    Some(rule)
                }
                _ => None,
            })
            .expect("instrumented unnamed rule not found");
        assert!(
            rule.name.len() > 256,
            "expected a long synthesized rule name"
        );

        let rule_name_vars = rule
            .head
            .0
            .iter()
            .filter_map(|action| match action {
                ResolvedAction::Let(_, var, ResolvedExpr::Lit(_, Literal::String(value)))
                    if value == &rule.name =>
                {
                    Some(var.name.as_str())
                }
                _ => None,
            })
            .collect::<Vec<_>>();
        assert_eq!(
            rule_name_vars.len(),
            1,
            "the synthesized rule name should be bound once in the actions"
        );
        let rule_name_var = rule_name_vars[0];

        // Proof constructors are relations, so a rule proof carrying its premises
        // inline is emitted as a `(let <id> (mint-@Rule_1! <rule-name> <premise>
        // <column>))` action — the rule has one body fact. Count those mints and
        // check they reuse the hoisted rule-name variable as their first
        // argument.
        let rule_uses = rule
            .head
            .0
            .iter()
            .filter(|action| {
                let Some((relation, args)) = mint_call(action) else {
                    return false;
                };
                if !rule_constructors.contains(relation) {
                    return false;
                }
                assert!(
                    matches!(
                        args.first(),
                        Some(ResolvedExpr::Var(_, var)) if var.name == rule_name_var
                    ),
                    "generated Rule constructor did not reuse the rule-name variable"
                );
                true
            })
            .count();
        assert!(
            rule_uses > 0,
            "expected the rule to emit a Rule constructor carrying its premises"
        );

        EGraph::new_with_proofs()
            .parse_and_run_program(None, source)
            .expect("hoisted rule-name proof should pass the checker");
    }

    /// A rule proof carries its premises inline, in a constructor declared per
    /// premise count ahead of the program that needs it. A program run in pieces
    /// must therefore declare the arities each piece introduces, not just the
    /// first.
    #[test]
    fn rule_premise_arities_are_declared_per_program() {
        let mut egraph = EGraph::new_with_proofs();
        egraph
            .parse_and_run_program(
                None,
                "(datatype Math (Add Math Math) (Num i64))
                 (rewrite (Add a b) (Add b a))",
            )
            .unwrap();
        assert!(
            !egraph
                .proof_state
                .proof_names
                .rule_fused_declared
                .contains(&2),
            "the first program has no two-premise rule, so it must not declare that arity"
        );
        // Two body facts, so a premise count the first program never declared.
        egraph
            .parse_and_run_program(
                None,
                "(relation Seed (Math))
                 (rule ((Seed x) (= x (Add a b))) ((union x (Add b (Add a b)))))
                 (Seed (Add (Num 1) (Num 2)))
                 (run 2)
                 (prove (= (Add (Num 1) (Num 2))
                           (Add (Num 2) (Add (Num 1) (Num 2)))))",
            )
            .unwrap();
        assert!(
            egraph
                .proof_state
                .proof_names
                .rule_fused_declared
                .contains(&2),
            "the second program's two-premise rule should have declared that arity"
        );
    }

    /// The encoder records one premise per body fact of the rule *after*
    /// `remove_globals` appends a lookup fact per global the head mentions —
    /// except the facts [`recomputable_premises`] gates out — while the proof
    /// checker replays the rule as written, without those facts. Proof conversion
    /// pairs premises with written facts by position, so the premise count must
    /// cover the written body's recorded facts, and the extras are exactly the
    /// trailing ones.
    #[test]
    fn rule_premises_cover_the_written_body_facts() {
        let source = r#"
            (datatype Math (Add Math Math) (Num i64))
            (relation Seen (Math))
            (let g (Num 7))
            ;; One written body fact, and a head that reads a global.
            (rule ((Seen x)) ((Seen (Add x g))) :name "with_global")
            ;; Two written body facts and no global.
            (rule ((Seen x) (= x (Add a b))) ((Seen a)) :name "without_global")
            ;; Three written body facts, of which the guard's premise is a
            ;; reflexive fiat over a base value, so no premise records it.
            (rule ((Seen x) (= x (Add (Num n) b)) (> n 0)) ((Seen b)) :name "with_guard")
            (Seen (Num 1))
            (run 2)
            (prove (Seen (Add (Num 1) (Num 7))))
        "#;

        // The rules as the checker replays them: before `remove_globals`.
        let mut checker = EGraph::new_with_proofs();
        checker.parse_and_run_program(None, source).unwrap();
        let written: HashMap<String, Vec<ResolvedFact>> = checker
            .proof_check_program
            .iter()
            .filter_map(|cmd| match cmd {
                GenericNCommand::NormRule { rule } => Some((rule.name.clone(), rule.body.clone())),
                _ => None,
            })
            .collect();

        // The rules as the encoder emits them: the premise count is the arity of
        // the `Rule_<k>` constructor each head writes.
        let mut encoder = EGraph::new_with_proofs();
        let commands = encoder.resolve_program(None, source).unwrap();
        let names = encoder.proof_state.proof_names.clone();
        let mut recorded: HashMap<String, usize> = HashMap::default();
        for command in &commands {
            let ResolvedCommand::Rule { rule } = command else {
                continue;
            };
            if !written.contains_key(&rule.name) {
                continue;
            }
            let premises = rule
                .head
                .0
                .iter()
                .filter_map(|action| names.fused_rule_arity(mint_call(action)?.0))
                .max()
                .unwrap_or_else(|| panic!("rule '{}' wrote no inline rule proof", rule.name));
            recorded.insert(rule.name.clone(), premises);
        }

        // Holds for every rule the checker replays, including the one `prove`
        // generates: conversion recomputes a gated premise instead of reading a
        // recorded one, so only the ungated facts need covering.
        for (name, premises) in &recorded {
            let facts = recomputable_premises(&written[name], &|_| false)
                .iter()
                .filter(|gated| !**gated)
                .count();
            assert!(
                *premises >= facts,
                "rule '{name}' recorded {premises} premises for a body of {facts} recorded facts"
            );
        }
        // Pin both sides of the inequality, so neither half can drift unnoticed:
        // the global reference adds exactly one trailing lookup fact, a rule
        // without one records exactly its written facts, and a gated fact records
        // none.
        assert_eq!(
            recorded.get("with_global").copied(),
            Some(written["with_global"].len() + 1),
            "a head reading a global should record one extra premise"
        );
        assert_eq!(
            recorded.get("without_global").copied(),
            Some(written["without_global"].len()),
            "a rule mentioning no global should record one premise per written fact"
        );
        assert_eq!(
            recorded.get("with_guard").copied(),
            Some(written["with_guard"].len() - 1),
            "a base-value guard should record no premise"
        );

        // The extras being *trailing* is what makes pairing by position correct,
        // and it rests entirely on `remove_globals` mapping the written facts in
        // place and appending the lookups after them. No written body here
        // mentions a global, so the mapping is the identity and the prefix
        // compares exactly.
        let removed = remove_globals(
            checker.proof_check_program.clone(),
            &mut SymbolGen::new("premise_order".to_string()),
        );
        let mut compared = 0;
        for command in &removed {
            let GenericNCommand::NormRule { rule } = command else {
                continue;
            };
            let before = &written[&rule.name];
            assert!(
                rule.body.len() >= before.len(),
                "`remove_globals` dropped a body fact of rule '{}'",
                rule.name
            );
            for (at, (after, before)) in rule.body.iter().zip(before).enumerate() {
                assert_eq!(
                    after, before,
                    "rule '{}' fact {at} is not the written one after `remove_globals`",
                    rule.name
                );
            }
            compared += 1;
        }
        assert_eq!(
            compared,
            written.len(),
            "every rule the checker replays should have been compared"
        );
    }

    /// An e-graph with proofs on and `proof-id`: a primitive returning an
    /// eq-sort value it was handed no container to read out of.
    fn proof_id_egraph() -> EGraph {
        let mut egraph = EGraph::default();
        let validator =
            |_: &mut TermDag, args: &[TermId]| -> Option<TermId> { args.first().copied() };
        add_primitive_with_validator!(
            &mut egraph,
            "proof-id" = |x: #| -> # { x },
            validator
        );
        egraph.with_proofs_enabled()
    }

    /// The prelude the `proof-id` rules below run against.
    const PROOF_ID_PRELUDE: &str = r#"
        (datatype Math
          (Done)
          (Num i64))
        (relation Seed (Math))
        (relation Seen (Math))

        (Seed (Num 1))
    "#;

    // An eq-sort value a primitive computes without being handed a container is
    // named by no view row, so there is no reflexive anchor for it. The premise
    // of the fact binding it *is* that anchor, so the rule is rejected whether
    // or not the actions read the value.
    #[test]
    fn proof_support_rejects_eq_sort_primitive_results_without_a_container() {
        for head in ["((Done))", "((Seen x))"] {
            let err = proof_id_egraph()
                .parse_and_run_program(
                    None,
                    &format!(
                        r#"{PROOF_ID_PRELUDE}
                        (rule ((Seed y)
                               (= x (proof-id y)))
                              {head}
                              :name "use-proof-id")
                        "#
                    ),
                )
                .unwrap_err();
            assert!(
                matches!(
                    err,
                    Error::UnsupportedProofCommand {
                        reason:
                            ProofEncodingUnsupportedReason::EqSortPrimitiveResultWithoutContainer,
                        ..
                    }
                ),
                "expected EqSortPrimitiveResultWithoutContainer for head {head}, got {err:?}"
            );
        }
    }

    // The same value, in a body position whose premise drops its anchor: a view
    // atom's argument, and the right-hand side of a term the query builds. Each
    // rule encodes, and the proof of what it concludes checks.
    #[test]
    fn proof_mode_allows_an_eq_sort_primitive_result_whose_anchor_goes_unread() {
        for body in [
            "(Seed (proof-id y))",
            "(= (Num n) (proof-id y))",
            // The value is also matched by a view atom, which anchors it.
            "(= x (proof-id y)) (Seed x)",
            // The value is aliased to a variable a view atom anchors.
            "(= x (proof-id y)) (Seed z) (= x z)",
        ] {
            proof_id_egraph()
                .parse_and_run_program(
                    None,
                    &format!(
                        r#"{PROOF_ID_PRELUDE}
                        (rule ((Seed y) {body})
                              ((Seen y))
                              :name "read-a-proof-id")
                        (run 1)
                        (prove (Seen (Num 1)))
                        "#
                    ),
                )
                .unwrap_or_else(|err| panic!("body `{body}` should encode, got {err:?}"));
        }
    }

    /// A guard reads its own expression's premise — there is no second side to
    /// drop it against — so a guard over an unanchored value must be rejected by
    /// proof support rather than reaching the encoder's anchor assertion.
    #[test]
    fn proof_support_rejects_a_guard_over_an_unanchored_value() {
        for (body, expected) in [
            (
                "(proof-id y)",
                ProofEncodingUnsupportedReason::EqSortPrimitiveResultWithoutContainer,
            ),
            (
                "(= v (vec-of y)) (vec-get v 0)",
                ProofEncodingUnsupportedReason::ContainerCreatedInQueryProvedAbout,
            ),
        ] {
            let err = proof_id_egraph()
                .parse_and_run_program(
                    None,
                    &format!(
                        r#"{PROOF_ID_PRELUDE}
                        (sort MathVec (Vec Math))
                        (rule ((Seed y) {body})
                              ((Seen y))
                              :name "guard-over-an-unanchored-value")
                        "#
                    ),
                )
                .unwrap_err();
            let reason = match &err {
                Error::UnsupportedProofCommand { reason, .. } => format!("{reason:?}"),
                other => panic!("expected an unsupported-proof error for `{body}`, got {other:?}"),
            };
            assert_eq!(
                reason,
                format!("{expected:?}"),
                "wrong rejection reason for guard `{body}`"
            );
        }
    }

    #[test]
    fn proof_support_rejects_naive_eq_sort_primitive_results_in_facts() {
        let err = proof_id_egraph()
            .parse_and_run_program(
                None,
                &format!(
                    r#"{PROOF_ID_PRELUDE}
                    (rule ((Seed y)
                           (= x (proof-id y)))
                          ((Done))
                          :naive
                          :name "naive-use-proof-id")
                    "#
                ),
            )
            .unwrap_err();

        assert!(
            matches!(
                err,
                Error::UnsupportedProofCommand {
                    reason: ProofEncodingUnsupportedReason::NaiveEqSortPrimitiveFact,
                    ..
                }
            ),
            "expected NaiveEqSortPrimitiveFact, got {err:?}"
        );
    }

    #[test]
    fn proof_mode_allows_eq_container_primitive_results_in_facts() {
        // A real (presort-declared) eq-container sort, so the term/proof
        // encoding builds its rebuild primitive. A custom identity primitive
        // returns an existing eq-container value, exercising the
        // eq-container-primitive-result-in-a-fact path under proofs.
        let mut egraph = EGraph::new_with_proofs();
        egraph
            .parse_and_run_program(
                None,
                r#"
                (datatype E (Mk))
                (sort EqContainer (Vec E))
                "#,
            )
            .unwrap();

        let eq_container_sort = egraph
            .type_info
            .get_sort_by_name("EqContainer")
            .expect("EqContainer sort")
            .clone();
        let validator =
            |_: &mut TermDag, args: &[TermId]| -> Option<TermId> { args.first().copied() };
        add_primitive_with_validator!(
            &mut egraph,
            "proof-container-id" = |x: # (eq_container_sort)| -> # (eq_container_sort) { x },
            validator
        );

        egraph
            .parse_and_run_program(
                None,
                r#"
                (relation SeedContainer (EqContainer))
                (relation Done ())

                (SeedContainer (vec-of (Mk)))

                (rule ((SeedContainer ys)
                       (= xs (proof-container-id ys)))
                      ((Done))
                      :name "use-proof-container-id")

                (run 1)
                (prove (Done))
                "#,
            )
            .unwrap();
    }

    #[test]
    #[should_panic(expected = "Primitive 'proof-container-reject' validation failed")]
    fn proof_checker_validates_container_primitive_facts() {
        let mut egraph = EGraph::new_with_proofs();
        egraph
            .parse_and_run_program(
                None,
                r#"
                (datatype E (Mk))
                (sort EqContainer (Vec E))
                "#,
            )
            .unwrap();

        let eq_container_sort = egraph
            .type_info
            .get_sort_by_name("EqContainer")
            .expect("EqContainer sort")
            .clone();
        let validator = |_: &mut TermDag, _: &[TermId]| -> Option<TermId> { None };
        add_primitive_with_validator!(
            &mut egraph,
            "proof-container-reject" = |x: # (eq_container_sort)| -> # (eq_container_sort) { x },
            validator
        );

        egraph
            .parse_and_run_program(
                None,
                r#"
                (relation SeedContainer (EqContainer))
                (relation Done ())

                (SeedContainer (vec-of (Mk)))

                (rule ((SeedContainer ys)
                       (proof-container-reject ys))
                      ((Done))
                      :name "reject-invalid-container-fact")

                (run 1)
                (prove (Done))
                "#,
            )
            .unwrap();
    }

    #[test]
    fn proof_extraction_skips_container_primitive_validation() {
        let mut egraph = EGraph::default().with_proof_extraction();
        egraph
            .parse_and_run_program(
                None,
                r#"
                (datatype E (Mk))
                (sort EqContainer (Vec E))
                "#,
            )
            .unwrap();

        let eq_container_sort = egraph
            .type_info
            .get_sort_by_name("EqContainer")
            .expect("EqContainer sort")
            .clone();
        let validator = |_: &mut TermDag, _: &[TermId]| -> Option<TermId> { None };
        add_primitive_with_validator!(
            &mut egraph,
            "proof-container-reject" = |x: # (eq_container_sort)| -> # (eq_container_sort) { x },
            validator
        );

        let outputs = egraph
            .parse_and_run_program(
                None,
                r#"
                (relation SeedContainer (EqContainer))
                (relation Done ())

                (SeedContainer (vec-of (Mk)))

                (rule ((SeedContainer ys)
                       (proof-container-reject ys))
                      ((Done))
                      :name "reject-invalid-container-fact")

                (run 1)
                (check (Done))
                "#,
            )
            .unwrap();
        assert!(
            outputs
                .iter()
                .any(|output| matches!(output, CommandOutput::ProveExists { .. }))
        );
    }

    #[test]
    fn proof_extraction_still_rejects_a_false_check() {
        let error = EGraph::default()
            .with_proof_extraction()
            .parse_and_run_program(
                None,
                r#"
                (relation Done ())
                (check (Done))
                "#,
            )
            .unwrap_err();

        assert!(
            matches!(
                error,
                Error::ProofError {
                    error: ProveExistsError::QueryDidNotMatch { .. },
                    ..
                }
            ),
            "expected QueryDidNotMatch, got {error:?}"
        );
    }

    // A container constructed in the query body and not used in an action: the
    // binding fact's proof is the container's reflexive `Eval`, which the rule
    // check re-derives with the typed primitive.
    #[test]
    fn proof_mode_query_constructed_container_not_used_in_action() {
        let mut egraph = EGraph::new_with_proofs();
        egraph
            .parse_and_run_program(
                None,
                r#"
                (datatype E (Mk))
                (sort EqContainer (Vec E))
                (relation SeedElem (E))
                (relation Done ())

                (SeedElem (Mk))

                (rule ((SeedElem e)
                       (= xs (vec-of e)))
                      ((Done))
                      :name "new-container-in-body")

                (run 1)
                (prove (Done))
                "#,
            )
            .unwrap();
    }

    // Two elements read out of a container a view row anchors: each read's
    // reflexive anchor is a projection off that row, so the fact between them
    // gets a real premise.
    #[test]
    fn proof_mode_equates_two_container_element_reads() {
        let mut egraph = EGraph::new_with_proofs();
        egraph
            .parse_and_run_program(
                None,
                r#"
                (datatype Math (Num i64))
                (sort MathVec (Vec Math))
                (constructor Holder (MathVec) Math)
                (Holder (vec-of (Num 1) (Num 1)))

                (rule ((= h (Holder v))
                       (= (vec-get v 0) (vec-get v 1)))
                      ((Num 99))
                      :name "elements-agree")

                (run 1)
                (prove (= (Num 99) (Num 99)))
                "#,
            )
            .unwrap();
    }

    // The same, with each read bound to a variable first: the variables are
    // aliased to the reads, so the anchor is found through the alias.
    #[test]
    fn proof_mode_equates_two_container_elements_bound_to_variables() {
        let mut egraph = EGraph::new_with_proofs();
        egraph
            .parse_and_run_program(
                None,
                r#"
                (datatype Math (Num i64))
                (sort MathVec (Vec Math))
                (constructor Holder (MathVec) Math)
                (Holder (vec-of (Num 1) (Num 1)))

                (rule ((= h (Holder v))
                       (= e (vec-get v 0))
                       (= f (vec-get v 1))
                       (= e f))
                      ((Num 99))
                      :name "element-variables-agree")

                (run 1)
                (prove (= (Num 99) (Num 99)))
                "#,
            )
            .unwrap();
    }

    // The same read against a term the query builds is not a side condition, so
    // the fact keeps a real premise rather than an `Eval` marker.
    #[test]
    fn proof_mode_proves_a_built_term_against_a_container_element_read() {
        let mut egraph = EGraph::new_with_proofs();
        egraph
            .parse_and_run_program(
                None,
                r#"
                (datatype Math (Num i64) (Add Math Math))
                (sort MathVec (Vec Math))
                (constructor Holder (MathVec) Math)
                (relation Seen (Math))
                (let $held (Holder (vec-of (Add (Num 1) (Num 2)) (Num 3))))

                (rule ((= h (Holder v))
                       (= (Add p q) (vec-get v 0)))
                      ((Seen h))
                      :name "sum-in-slot-zero")

                (run 1)
                (prove (Seen $held))
                "#,
            )
            .unwrap();
    }

    // A container constructed in the query is a side condition with no carryable
    // proof (just an `Eval` marker), so it can't be used in an action. Proof mode
    // rejects such a rule rather than producing an unsound proof.
    #[test]
    fn proof_support_rejects_query_constructed_container_used_in_action() {
        let mut egraph = EGraph::new_with_proofs();
        let err = egraph
            .parse_and_run_program(
                None,
                r#"
                (datatype E (Mk))
                (sort EqContainer (Vec E))
                (relation SeedElem (E))
                (relation Out (EqContainer))

                (rule ((SeedElem e)
                       (= xs (vec-of e)))
                      ((Out xs))
                      :name "new-container-in-action")
                "#,
            )
            .unwrap_err();
        assert!(
            matches!(
                err,
                Error::UnsupportedProofCommand {
                    reason: ProofEncodingUnsupportedReason::ContainerCreatedInQueryUsedInAction,
                    ..
                }
            ),
            "expected ContainerCreatedInQueryUsedInAction, got {err:?}"
        );
    }

    /// Run `program` under proofs and return the reason it was rejected.
    fn proof_rejection_reason(program: &str) -> ProofEncodingUnsupportedReason {
        let err = EGraph::new_with_proofs()
            .parse_and_run_program(None, program)
            .unwrap_err();
        match err {
            Error::UnsupportedProofCommand { reason, .. } => reason,
            other => panic!("expected UnsupportedProofCommand, got {other:?}"),
        }
    }

    /// The rules below all read an eq-sort value out of a container the query
    /// itself built. Nothing anchors such a container — no view row mentions it —
    /// so the encoding has no proof to project the value out of.
    fn assert_query_built_container_rejected(program: &str) {
        let reason = proof_rejection_reason(program);
        assert!(
            matches!(
                reason,
                ProofEncodingUnsupportedReason::ContainerCreatedInQueryProvedAbout
            ),
            "expected ContainerCreatedInQueryProvedAbout, got {reason:?}"
        );
    }

    // The premise of the fact binding the element *is* its reflexive anchor, so
    // the rule is rejected whether or not the actions read the element.
    #[test]
    fn proof_support_rejects_element_read_from_query_built_container() {
        for head in ["((Seen e))", "((Seen a))"] {
            assert_query_built_container_rejected(&format!(
                r#"
                (datatype Math (Num i64))
                (sort MathVec (Vec Math))
                (relation HasElem (Math))
                (relation Seen (Math))

                (rule ((HasElem a) (HasElem b)
                       (= xs (vec-of a b))
                       (= e (vec-get xs 1)))
                      {head}
                      :name "read-out-of-a-built-vec")
                "#
            ));
        }
    }

    // The same read, in a body position whose premise drops its anchor: a view
    // atom's argument, and the right-hand side of a term the query builds. Each
    // rule encodes, and the proof of what it concludes checks.
    #[test]
    fn proof_mode_reads_a_query_built_container_element_whose_anchor_goes_unread() {
        for body in [
            "(HasElem (vec-get xs 1))",
            "(= (Num n) (vec-get xs 1))",
            // The element is also matched by a view atom, which anchors it.
            "(= e (vec-get xs 1)) (HasElem e)",
            // The element is aliased to a variable a view atom anchors.
            "(= e (vec-get xs 1)) (HasElem z) (= e z)",
        ] {
            EGraph::new_with_proofs()
                .parse_and_run_program(
                    None,
                    &format!(
                        r#"
                        (datatype Math (Num i64))
                        (sort MathVec (Vec Math))
                        (relation HasElem (Math))
                        (relation Seen (Math))
                        (HasElem (Num 1))

                        (rule ((HasElem a) (HasElem b) (= xs (vec-of a b)) {body})
                              ((Seen a))
                              :name "read-out-of-a-built-vec")

                        (run 1)
                        (prove (Seen (Num 1)))
                        "#
                    ),
                )
                .unwrap_or_else(|err| panic!("body `{body}` should encode, got {err:?}"));
        }
    }

    #[test]
    fn proof_support_rejects_element_reads_equated_from_query_built_container() {
        assert_query_built_container_rejected(
            r#"
            (datatype Math (Num i64))
            (sort MathVec (Vec Math))
            (constructor Holder (MathVec) Math)

            (rule ((= h (Holder v))
                   (= ys (vec-of (vec-get v 0) (vec-get v 0)))
                   (= (vec-get ys 0) (vec-get ys 1)))
                  ((Num 99))
                  :name "built-vec-elements-agree")
            "#,
        );
    }

    #[test]
    fn proof_support_rejects_element_variables_from_query_built_container() {
        assert_query_built_container_rejected(
            r#"
            (datatype Math (Num i64))
            (sort MathVec (Vec Math))
            (constructor Holder (MathVec) Math)

            (rule ((= h (Holder v))
                   (= ys (vec-of (vec-get v 0) (vec-get v 0)))
                   (= e (vec-get ys 0))
                   (= f (vec-get ys 1))
                   (= e f))
                  ((Num 99))
                  :name "built-vec-element-variables-agree")
            "#,
        );
    }

    #[test]
    fn proof_support_rejects_two_query_built_containers_equated() {
        assert_query_built_container_rejected(
            r#"
            (datatype Math (Num i64))
            (sort MathVec (Vec Math))
            (constructor Holder (MathVec) Math)

            (rule ((= h (Holder v))
                   (= ys (vec-of (vec-get v 0)))
                   (= zs (vec-of (vec-get v 0)))
                   (= ys zs))
                  ((Num 99))
                  :name "built-vecs-agree")
            "#,
        );
    }

    // A container the query built is still free to produce a base-sorted value,
    // which needs no proof about the container.
    #[test]
    fn proof_mode_reads_a_base_value_out_of_a_query_built_container() {
        let mut egraph = EGraph::new_with_proofs();
        egraph
            .parse_and_run_program(
                None,
                r#"
                (datatype Math (Num i64))
                (sort MathVec (Vec Math))
                (relation HasElem (Math))
                (relation Len (i64))
                (HasElem (Num 1))

                (rule ((HasElem a) (= xs (vec-of a a)) (= n (vec-length xs)))
                      ((Len n))
                      :name "length-of-a-built-vec")

                (run 1)
                (prove (Len 2))
                "#,
            )
            .unwrap();
    }

    /// A `subsume` may arrive in a batch long after the datatype's, so the
    /// scaffolding cannot be emitted by a pass over the whole program.
    #[test]
    fn subsume_declared_in_a_later_batch() {
        let mut egraph = EGraph::new_with_term_encoding();
        egraph
            .parse_and_run_program(None, "(datatype Math (Num i64) (Add Math Math))")
            .unwrap();
        egraph
            .parse_and_run_program(None, "(Add (Num 1) (Num 2))")
            .unwrap();
        egraph
            .parse_and_run_program(None, "(subsume (Add (Num 1) (Num 2)))")
            .unwrap();
        // A subsumed row is excluded from matching but still present.
        egraph
            .parse_and_run_program(
                None,
                r#"
                (rule ((= x (Add a b))) ((panic "a subsumed row matched")))
                (run 1)
                (check (= (Add (Num 1) (Num 2)) (Add (Num 1) (Num 2))))
                "#,
            )
            .unwrap();
    }

    /// `push` clones the whole [`EGraph`], so the memo saying a function's
    /// subsumption scaffolding is declared rolls back with the declaration it
    /// tracks: subsuming the same function again after the `pop` re-declares it.
    #[test]
    fn subsume_scaffolding_survives_push_pop() {
        let mut egraph = EGraph::new_with_term_encoding();
        egraph
            .parse_and_run_program(
                None,
                r#"
                (datatype Math (Num i64) (Add Math Math))
                (Add (Num 1) (Num 2))
                (push)
                (subsume (Add (Num 1) (Num 2)))
                (pop)
                (subsume (Add (Num 1) (Num 2)))
                "#,
            )
            .unwrap();
        egraph
            .parse_and_run_program(
                None,
                r#"
                (rule ((= x (Add a b))) ((panic "a subsumed row matched")))
                (run 1)
                "#,
            )
            .unwrap();
    }

    /// The same, for a `delete` — which needs no scaffolding at all.
    #[test]
    fn delete_across_push_pop_and_later_batches() {
        let mut egraph = EGraph::new_with_term_encoding();
        egraph
            .parse_and_run_program(None, "(datatype Math (Num i64) (Add Math Math))")
            .unwrap();
        egraph
            .parse_and_run_program(
                None,
                r#"
                (Add (Num 1) (Num 2))
                (push)
                (delete (Add (Num 1) (Num 2)))
                (pop)
                "#,
            )
            .unwrap();
        // The pop restored the row, so the later delete has something to remove.
        egraph
            .parse_and_run_program(
                None,
                r#"
                (check (= (Add (Num 1) (Num 2)) (Add (Num 1) (Num 2))))
                (delete (Add (Num 1) (Num 2)))
                (fail (check (= (Add (Num 1) (Num 2)) (Add (Num 1) (Num 2)))))
                "#,
            )
            .unwrap();
    }

    /// The encoded `delete` keeps the uninstrumented meaning: execution stages
    /// removals and applies them ahead of the insertions committed in the same
    /// batch, so a row another rule inserts in that batch survives the delete.
    #[test]
    fn delete_loses_to_a_same_batch_insert() {
        for mut egraph in [EGraph::default(), EGraph::new_with_term_encoding()] {
            let outputs = egraph
                .parse_and_run_program(
                    None,
                    r#"
                    (function F (i64) i64 :no-merge)
                    (relation Go ())
                    (Go)
                    (rule ((Go)) ((set (F 2) 20)) :name "inserter")
                    (rule ((Go)) ((delete (F 2))) :name "deleter")
                    (run 1)
                    (print-size F)
                    "#,
                )
                .unwrap();
            let sizes: Vec<usize> = outputs
                .iter()
                .filter_map(|output| match output {
                    CommandOutput::PrintFunctionSize(size) => Some(*size),
                    _ => None,
                })
                .collect();
            assert_eq!(sizes, vec![1]);
        }
    }

    #[test]
    fn doc_example_add_function2() {
        let commands = term_encode(
            r#"
            (function add (i64 i64) i64 :merge old)
            (check (= (add 0 0) 0))
            "#,
        );

        let snapshot = sanitize_internal_names(&commands)
            .iter()
            .map(|cmd| cmd.to_string())
            .collect::<Vec<_>>()
            .join("\n");

        insta::assert_snapshot!("doc_example_add_function2", snapshot);
    }

    #[test]
    fn doc_example_add_function1() {
        let commands = term_encode(
            r#"
(sort Math)
(constructor Add (i64 i64) Math)
(Add 1 2)
(rule ((Add a b))
      ((union (Add a b) (Add b a)))
     :name "commutativity")
(check (= (Add 1 2) (Add 2 1)))
            "#,
        );

        let snapshot = sanitize_internal_names(&commands)
            .iter()
            .map(|cmd| cmd.to_string())
            .collect::<Vec<_>>()
            .join("\n");

        insta::assert_snapshot!("doc_example_add_function1", snapshot);
    }

    /// `doc_example_add_function1` with the same shape over eq-sort children, so
    /// the snapshot shows what a view's child columns cost: one declared index
    /// and one rebuild rule per eq-sort column, rather than only the output's.
    #[test]
    fn doc_example_add_eqsort_children() {
        let commands = term_encode(
            r#"
(sort Math)
(constructor Num (i64) Math)
(constructor Add (Math Math) Math)
(Add (Num 1) (Num 2))
(rule ((Add a b))
      ((union (Add a b) (Add b a)))
     :name "commutativity")
(check (= (Add (Num 1) (Num 2)) (Add (Num 2) (Num 1))))
            "#,
        );

        let snapshot = sanitize_internal_names(&commands)
            .iter()
            .map(|cmd| cmd.to_string())
            .collect::<Vec<_>>()
            .join("\n");

        insta::assert_snapshot!("doc_example_add_eqsort_children", snapshot);
    }

    #[test]
    fn generated_path_compression_executes_in_all_encoding_modes() {
        for mode in 0..3 {
            for seminaive in [false, true] {
                let (mut egraph, proof_mode) = match mode {
                    0 => (EGraph::new_with_term_encoding(), false),
                    1 => (EGraph::new_with_proofs(), true),
                    2 => (EGraph::default().with_proof_extraction(), true),
                    _ => unreachable!(),
                };
                egraph.seminaive = seminaive;
                let assertion = if proof_mode {
                    "(prove (= (A) (C)))"
                } else {
                    "(check (= (A) (C)))"
                };
                let outputs = egraph
                    .parse_and_run_program(
                        Some(format!("path-compression-{proof_mode}-{seminaive}.egg")),
                        &format!(
                            r#"
                            (sort Pc)
                            (constructor A () Pc)
                            (constructor B () Pc)
                            (constructor C () Pc)
                            (A)
                            (B)
                            (C)
                            (union (B) (C))
                            (union (A) (B))
                            (run 1)
                            {assertion}
                            "#
                        ),
                    )
                    .unwrap();
                assert_eq!(
                    outputs
                        .iter()
                        .filter(|output| matches!(output, CommandOutput::ProveExists { .. }))
                        .count(),
                    usize::from(proof_mode)
                );
                assert!(
                    egraph
                        .get_function_names()
                        .iter()
                        .any(|name| name == "@UF_Pc")
                );
                assert!(egraph.num_tuples() > 0);
                assert!(
                    egraph
                        .get_overall_run_report()
                        .num_matches_per_rule
                        .iter()
                        .any(|(name, count)| name.contains("@uf_path_compress") && *count > 0),
                    "generated path compression did not execute in proof_mode={proof_mode}, seminaive={seminaive}"
                );
            }
        }
    }

    #[test]
    fn generated_extract_input_and_output_have_exact_runtime_effects() {
        let directory = std::env::temp_dir().join(format!(
            "egglog-generated-command-effects-{}-{}",
            std::process::id(),
            line!()
        ));
        std::fs::remove_dir_all(&directory).ok();
        std::fs::create_dir_all(&directory).unwrap();
        std::fs::write(directory.join("loaded.tsv"), "7\t8\n").unwrap();

        let mut egraph = EGraph::new_with_proofs();
        egraph.fact_directory = Some(directory.clone());
        egraph
            .parse_and_run_program(
                None,
                r#"
                (sort RuntimeExpr)
                (constructor RuntimeNum (i64) RuntimeExpr)
                (constructor RuntimeAdd (RuntimeExpr RuntimeExpr) RuntimeExpr)
                (function RuntimeLoaded (i64) i64 :merge old)
                "#,
            )
            .unwrap();

        let outputs = egraph
            .parse_and_run_program(
                None,
                "(extract (RuntimeAdd (RuntimeNum 1) (RuntimeNum 2)) 0)",
            )
            .unwrap();
        assert_eq!(outputs.len(), 3);
        assert!(matches!(outputs[0], CommandOutput::RunSchedule(_)));
        let CommandOutput::ExtractBest(ref dag, cost, term) = outputs[1] else {
            panic!("expected ExtractBest between generated schedules")
        };
        assert_eq!(
            dag.to_string(term),
            "(RuntimeAdd (RuntimeNum 1) (RuntimeNum 2))"
        );
        assert_eq!(cost, 5);
        assert!(matches!(outputs[2], CommandOutput::RunSchedule(_)));

        let before_input = egraph.num_tuples();
        let outputs = egraph
            .parse_and_run_program(None, "(input RuntimeLoaded \"loaded.tsv\")")
            .unwrap();
        assert!(
            outputs
                .iter()
                .all(|output| matches!(output, CommandOutput::RunSchedule(_)))
        );
        assert_eq!(egraph.num_tuples(), before_input + 3);
        egraph
            .parse_and_run_program(None, "(check (= (RuntimeLoaded 7) 8))")
            .unwrap();
        assert_eq!(
            std::fs::read_to_string(directory.join("loaded.tsv")).unwrap(),
            "7\t8\n"
        );

        let before_output = egraph.num_tuples();
        let outputs = egraph
            .parse_and_run_program(None, "(output \"result.txt\" (+ 1 2))")
            .unwrap();
        assert_eq!(outputs.len(), 1);
        assert!(matches!(outputs[0], CommandOutput::RunSchedule(_)));
        assert_eq!(egraph.num_tuples(), before_output);
        assert_eq!(
            std::fs::read_to_string(directory.join("result.txt")).unwrap(),
            "3\n"
        );

        std::fs::remove_dir_all(directory).unwrap();
    }

    #[test]
    fn generated_extract_input_and_output_preserve_failure_boundaries() {
        let directory = std::env::temp_dir().join(format!(
            "egglog-generated-command-errors-{}-{}",
            std::process::id(),
            line!()
        ));
        std::fs::remove_dir_all(&directory).ok();
        std::fs::create_dir_all(&directory).unwrap();
        std::fs::write(directory.join("malformed.tsv"), "7\n").unwrap();

        let mut egraph = EGraph::new_with_term_encoding();
        egraph.fact_directory = Some(directory.clone());
        egraph
            .parse_and_run_program(
                None,
                r#"
                (sort RuntimeExpr)
                (constructor RuntimeNum (i64) RuntimeExpr)
                (constructor RuntimeAdd (RuntimeExpr RuntimeExpr) RuntimeExpr)
                (function RuntimeLoaded (i64) i64 :merge old)
                "#,
            )
            .unwrap();

        let error = egraph
            .parse_and_run_program(None, "(extract (RuntimeNum 1) -1)")
            .unwrap_err();
        assert!(matches!(
            error,
            Error::ExtractError(ref message)
                if message == "cannot extract a negative number of variants"
        ));

        let before_input = (
            egraph.num_tuples(),
            egraph.get_function_names(),
            egraph.parser.symbol_gen.clone(),
        );
        let error = egraph
            .parse_and_run_program(None, "(input RuntimeLoaded \"malformed.tsv\")")
            .unwrap_err();
        assert!(matches!(
            error,
            Error::InputFileFormatError(ref file) if file == "malformed.tsv"
        ));
        assert_eq!(
            (
                egraph.num_tuples(),
                egraph.get_function_names(),
                egraph.parser.symbol_gen.clone(),
            ),
            before_input
        );

        let before_output = (egraph.num_tuples(), egraph.parser.symbol_gen.clone());
        let error = egraph
            .parse_and_run_program(None, "(output \"must-not-exist.txt\" (RuntimeNum 1))")
            .unwrap_err();
        assert!(
            matches!(
                error,
                Error::TypeError(TypeError::UnresolvedPrimitive {
                    ref name,
                    ctx: crate::Context::Full,
                    ref span,
                }) if name == "RuntimeNum" && span.string() == "(RuntimeNum 1)"
            ),
            "unexpected native output binding error: {error:?}"
        );
        assert!(!directory.join("must-not-exist.txt").exists());
        assert_eq!(
            (egraph.num_tuples(), egraph.parser.symbol_gen.clone()),
            before_output
        );

        std::fs::remove_dir_all(directory).unwrap();
    }

    #[test]
    fn generated_source_rule_panic_keeps_the_seed() {
        let mut egraph = EGraph::new_with_term_encoding();
        let error = egraph
            .parse_and_run_program(
                None,
                r#"
                (relation PanicSeed ())
                (PanicSeed)
                (rule ((PanicSeed))
                      ((panic "typed-rule-boom"))
                      :name "typed-panic-rule")
                (run 1)
                "#,
            )
            .unwrap_err();
        assert!(
            matches!(
                error,
                Error::BackendError(ref message) if message.contains("typed-rule-boom")
            ),
            "unexpected panic-rule error: {error:?}"
        );
        egraph
            .parse_and_run_program(None, "(check (PanicSeed))")
            .unwrap();
    }

    #[test]
    fn generated_binding_errors_keep_source_spans_through_fail() {
        let make_egraph = |header| {
            let mut egraph = EGraph::new_with_term_encoding();
            egraph.resolve_program(None, header).unwrap();
            add_primitive!(&mut egraph, "!=" = |a: #, b: #| -?> () {
                (a != b).then_some(())
            });
            egraph
        };

        for (header, source, expected_span) in [
            (
                "(relation ErrorHeader (i64))",
                "(sort Broken)",
                "(sort Broken)",
            ),
            (
                "(relation NestedErrorHeader (i64))",
                "(fail (sort NestedBroken))",
                "(sort NestedBroken)",
            ),
        ] {
            let error = make_egraph(header)
                .parse_and_run_program(Some("generated-binding-span.egg".to_owned()), source)
                .unwrap_err();
            assert!(
                matches!(
                    error,
                    Error::TypeError(TypeError::AmbiguousPrimitive {
                        ref name,
                        ctx: crate::Context::Pure,
                        ref span,
                    }) if name == "!=" && span.string() == expected_span
                ),
                "unexpected generated binding error for {source}: {error:?}"
            );
        }
    }
}
