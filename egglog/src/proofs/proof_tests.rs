#[cfg(test)]
mod tests {
    use crate::ast::{
        GenericAction, GenericNCommand, Literal, ResolvedAction, ResolvedCommand, ResolvedExpr,
        ResolvedFact, RuleEvalMode, remove_globals::remove_globals, sanitize_internal_names,
    };
    use crate::core::ResolvedCall;
    use crate::proofs::proof_checker::eval_expr_with_subst;
    use crate::proofs::proof_extraction::ProveExistsError;
    use crate::proofs::proof_format::{ProofId, ProofStore, Proposition};
    use crate::proofs::proof_head::{Firing, HeadPlan, HeadProof, ProofAlgebra};
    use crate::util::{HashMap, HashSet, IndexMap, SymbolGen};
    use crate::{
        CommandOutput, EGraph, Error, ProofEncodingUnsupportedReason, TermDag, TermId,
        add_primitive_with_validator,
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
            // Every rule proof row the head writes: `(set (Rule_k … col fresh) ())`
            // or `(set (RuleLink prev bridge col fresh) ())`. The column sits just
            // ahead of the minted id, as a literal or as the `proof-of-max` over
            // the two columns a `union` orients between.
            let columns: Vec<i64> = rule
                .head
                .0
                .iter()
                .filter_map(|action| match action {
                    ResolvedAction::Set(_, ResolvedCall::Func(func), args, _)
                        if names.fused_rule_arity(&func.name).is_some()
                            || func.name == names.rule_link_constructor =>
                    {
                        args.get(args.len().checked_sub(2)?)
                    }
                    _ => None,
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

    /// The encoding reads `@UF` and `term_proof` from rule actions under
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
        // The second case binds an eq-sort body var, whose `term_proof` RHS
        // read would otherwise force `:unsafe-seminaive`. Both must stay naive.
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

        // Proof constructors are relations, so each rule proof is emitted as a
        // `(set (@Rule_1 <rule-name> <premise> <column> <id>) ())` action — the rule
        // has one body fact — not a call expression. Count those set actions and
        // check they reuse the hoisted rule-name variable as their first argument.
        let rule_uses = rule
            .head
            .0
            .iter()
            .filter(|action| match action {
                ResolvedAction::Set(_, ResolvedCall::Func(func), args, _)
                    if rule_constructors.contains(&func.name) =>
                {
                    assert!(
                        matches!(
                            args.first(),
                            Some(ResolvedExpr::Var(_, var)) if var.name == rule_name_var
                        ),
                        "generated Rule constructor did not reuse the rule-name variable"
                    );
                    true
                }
                _ => false,
            })
            .count();
        assert!(
            rule_uses > 1,
            "expected the multi-action rule to emit multiple Rule constructors"
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
    /// `remove_globals` appends a lookup fact per global the head mentions, while
    /// the proof checker replays the rule as written, without those facts. Proof
    /// conversion pairs premises with written facts by position, so the premise
    /// count must cover the written body — the extras are exactly the trailing
    /// ones.
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
                .filter_map(|action| match action {
                    ResolvedAction::Set(_, ResolvedCall::Func(func), _, _) => {
                        names.fused_rule_arity(&func.name)
                    }
                    _ => None,
                })
                .max()
                .unwrap_or_else(|| panic!("rule '{}' wrote no inline rule proof", rule.name));
            recorded.insert(rule.name.clone(), premises);
        }

        // Holds for every rule the checker replays, including the one `prove`
        // generates.
        for (name, premises) in &recorded {
            let facts = written[name].len();
            assert!(
                *premises >= facts,
                "rule '{name}' recorded {premises} premises for a body of {facts} written facts"
            );
        }
        // Pin both sides of the inequality, so neither half can drift unnoticed:
        // the global reference adds exactly one trailing lookup fact, and a rule
        // without one records exactly its written facts.
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

        // The extras being *trailing* is what makes pairing by position correct,
        // and it rests entirely on `remove_globals` mapping the written facts in
        // place and appending the lookups after them. No written body here
        // mentions a global, so the mapping is the identity and the prefix
        // compares exactly.
        let removed = remove_globals(
            checker.proof_check_program.clone(),
            &mut SymbolGen::new("premise_order".to_string()),
            &mut Default::default(),
            checker
                .type_info()
                .get_sort_by_name("i64")
                .expect("the i64 sort is always registered")
                .clone(),
            true,
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

    #[test]
    fn proof_mode_allows_eq_sort_primitive_results_in_facts() {
        let mut egraph = EGraph::default();
        let validator =
            |_: &mut TermDag, args: &[TermId]| -> Option<TermId> { args.first().copied() };
        add_primitive_with_validator!(
            &mut egraph,
            "proof-id" = |x: #| -> # { x },
            validator
        );
        let mut egraph = egraph.with_proofs_enabled();

        egraph
            .parse_and_run_program(
                None,
                r#"
                (datatype Math
                  (Done)
                  (Num i64))
                (relation Seed (Math))

                (Seed (Num 1))

                (rule ((Seed y)
                       (= x (proof-id y)))
                      ((Done))
                      :name "use-proof-id")

                (run 1)
                (prove (Done))
                "#,
            )
            .unwrap();
    }

    #[test]
    fn proof_support_rejects_naive_eq_sort_primitive_results_in_facts() {
        let mut egraph = EGraph::default();
        let validator =
            |_: &mut TermDag, args: &[TermId]| -> Option<TermId> { args.first().copied() };
        add_primitive_with_validator!(
            &mut egraph,
            "proof-id" = |x: #| -> # { x },
            validator
        );
        let mut egraph = egraph.with_proofs_enabled();

        let err = egraph
            .parse_and_run_program(
                None,
                r#"
                (datatype Math
                  (Done)
                  (Num i64))
                (relation Seed (Math))

                (rule ((Seed y)
                       (= x (proof-id y)))
                      ((Done))
                      :naive
                      :name "naive-use-proof-id")
                "#,
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
}
