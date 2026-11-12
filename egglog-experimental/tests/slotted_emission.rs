use egglog_experimental::slotted::{Compiler, Options, ProofMode};

#[test]
fn generated_names_remain_reserved_across_inputs_and_restore_on_pop() {
    for proof_mode in [ProofMode::Disabled, ProofMode::Check, ProofMode::Prove] {
        let mut compiler = Compiler::new(Options {
            proof_mode,
            ..Default::default()
        });
        compiler
            .compile(None, "(datatype U (V Var) (N i64))")
            .unwrap();
        compiler
            .compile(None, "(push) (constructor F (U) U)")
            .unwrap();

        let mut reserved = vec![
            "GroupIdx",
            "SlottedSlotLayout",
            "slotted-shape",
            "GroupReplace_0",
            "Invocation_0",
            "_pinned_F",
        ];
        if proof_mode == ProofMode::Disabled {
            reserved.extend([
                "SubstMemoClass_FreeVars_0",
                "SubstMemoFrame_FreeVars_0",
                "_shape_F",
                "_shapeof_F",
            ]);
        } else {
            reserved.extend([
                "_shape_class_F",
                "_shape_back_F",
                "_shapeof_edges_F",
                "_shapeof_syms_F",
            ]);
        }
        for name in reserved {
            let error = compiler
                .compile(
                    Some("collision.egg".into()),
                    &format!("(relation {name} ())"),
                )
                .unwrap_err()
                .to_string();
            assert!(
                error.contains("reserved by the slotted encoding"),
                "{name}: {error}"
            );
            assert!(error.contains("collision.egg"), "{error}");
        }

        // Popping releases only the scoped constructor's generated names. A
        // later constructor must also reject a name declared in earlier input.
        compiler
            .compile(None, "(pop) (relation _pinned_F ())")
            .unwrap();
        assert!(compiler.compile(None, "(constructor F (U) U)").is_err());
        assert!(compiler.compile(None, "(relation GroupIdx ())").is_err());
        // Neither failed input commits its newly generated declarations.
        compiler.compile(None, "(relation _shapeof_F ())").unwrap();
        compiler.compile(None, "(constructor G (U) U)").unwrap();
    }
}
