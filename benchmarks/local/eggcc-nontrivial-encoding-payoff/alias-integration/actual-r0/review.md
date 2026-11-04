# Independent read-only source review

The bounded reviewer inspected the initial copied source, retained design and source input without edits, builds or tests. It found no demonstrated wrong-code case on the frozen input. The one-shot token lifetime, exact two pointer-invariant equations, allocation identity and free-state checks were appropriate.

The initial implementation did not satisfy the experiment contract: the private graph was independent of the certificate, PrimitiveOnly emitted constant equal receipts, the exact inner If true-branch ancestry join was absent, and signature/effect/root-context checks did not establish the advertised closed profile. The single revision addresses those points but still rejects the positive graph because its strict Expr-row whitelist omits the auxiliary TupleRemoveAt and to-hoist rows. This is an implementation admission failure, not a semantic counterexample, existing compiler bug, or impossibility result about the law.

No further functional revision is taken within the prescribed budget. The actual compiler controls must therefore be interpreted as fail-closed endpoint checks, not successful causal ablations.
